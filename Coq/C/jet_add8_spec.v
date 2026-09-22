(** Full C-to-Simplicity equivalence for add_8, from initial frame predicates.
    The 16 input bits and 9 output bits each fit within one backing word;
    surrounding input bits and initial output contents are unrestricted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_spec C.jet_read8_position.
Require Import C.jet_frame_spec C.jet_word_decode C.jet_increment8_word C.jet_increment8_spec.
Require Import C.jet_add8_call C.jet_add8_update C.jet_add8_word.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition word8_payload_at (w : int64) (cursor : Z) (payload : int64) : Prop :=
  Int64.zero_ext 8 (Int64.shru w (Int64.repr (56 - cursor))) =
    Int64.zero_ext 8 payload.

Definition single_word_pair_input_at (m : mem) (bf bw : block) (cursor : Z)
    (x y : Ty.tySem Word8) : Prop :=
  frame_fields m bf bw 8 cursor /\ 0 <= cursor <= 48 /\
  exists w, Mem.load Mint64 m bw 0 = Some (Vlong w) /\
    word8_payload_at w cursor (encode_word8 x) /\
    word8_payload_at w (cursor + 8) (encode_word8 y).

Lemma word8_payload_at_decode w cursor x :
  word8_payload_at w cursor (encode_word8 x) ->
  decode_word8 (Int64.shru w (Int64.repr (56 - cursor))) = x.
Proof.
  intros H. rewrite <- decode_word8_projection, H.
  rewrite decode_word8_projection. apply decode_word8_encode.
Qed.

Theorem eval_add8_cursors_matches_spec m bd bs bi bw
    (x y : Ty.tySem Word8) cursor read_cursor :
  9 <= cursor <= 64 ->
  single_word_pair_input_at m bs bi read_cursor x y ->
  single_word_output m bd bw cursor ->
  exists mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_add_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    decode_carry_word8 (Int64.shru output (Int64.repr (cursor - 9))) =
      @add8_spec Alg.CoreFunSem (x, y) /\
    (forall old, Mem.load Mint64 m bw 0 = Some (Vlong old) ->
      word_outside_eq 0 cursor output old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (cursor - 9))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HC [[HSE HSO] [HR [input [HI [HX HY]]]]]
    [[HDE HDO] [HN [HDw [PD [PW [old HW]]]]]].
  destruct (eval_add8_position_call m bd bs bi bw input old cursor read_cursor
    HR HC HSE HSO HI HDE HDO HW PD PW HDw)
    as [mf [Hcall [Hout [Hoff Hmem]]]].
  exists mf, (add8_word_at cursor old (read8_at read_cursor input)
    (read8_at (read_cursor + 8) input)).
  split; [exact Hcall |]. split; [exact Hout |]. split.
  - unfold read8_at. rewrite add8_word_at_spec by exact HC.
    rewrite (word8_payload_at_decode _ _ _ HX), (word8_payload_at_decode _ _ _ HY).
    reflexivity.
  - split.
    + intros old' HW'. assert (old' = old) by congruence. subst old'.
      apply add8_word_at_prefix; exact HC.
    + split; assumption.
Qed.

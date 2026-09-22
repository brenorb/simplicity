(** Public implementation-to-Simplicity theorem with arbitrary input padding
    and every non-crossing output cursor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word C.jet_exec C.jet_read8 C.jet_spec C.jets.
Require Import C.jet_increment8_spec C.jet_increment8_position_call C.jet_increment8_position_update.
Require Import C.jet_increment8_word C.jet_frame_spec C.jet_increment8_position_word.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_increment8_position_matches_spec m bd bs bi bw (x : Ty.tySem Word8) cursor :
  9 <= cursor <= 64 ->
  single_word_input m bs bi 8 (encode_word8 x) ->
  single_word_output m bd bw cursor ->
  exists mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_increment_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    decode_increment8 (Int64.shru output (Int64.repr (cursor - 9))) = @increment8_spec Alg.CoreFunSem x /\
    (forall old, Mem.load Mint64 m bw 0 = Some (Vlong old) ->
      word_outside_eq 0 cursor output old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (cursor - 9))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HCurs HI [[HE HO] [HN [HDw [PD [PW [old HW]]]]]].
  destruct (single_word_input_decode m bs bi x HI)
    as [input [[HSE HSO] [Hinput Hdecode]]].
  destruct (eval_increment8_position_call m bd bs bi bw input old cursor HCurs
    HSE HSO Hinput HE HO HW PD PW HDw) as [mf [HC [Hout [Hoff Hmem]]]].
  exists mf, (increment8_word_at cursor old (read8_result input)).
  split; [exact HC |]. split; [exact Hout |].
  split.
  - rewrite increment8_word_at_decode by exact HCurs.
    rewrite increment8_word_update_spec, Hdecode. reflexivity.
  - split.
    + intros old' HW'. assert (old' = old) by congruence. subst old'.
      apply increment8_word_at_prefix; exact HCurs.
    + split; assumption.
Qed.

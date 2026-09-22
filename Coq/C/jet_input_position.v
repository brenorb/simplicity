(** Single-word input slices at any non-crossing read cursor. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Memory.
Require Import Simplicity.Word C.jet_frame_spec C.jet_spec C.jet_word_decode
  C.jet_increment8_word C.jet_increment8_spec.
Import Values Mem.
Local Open Scope Z_scope.

Definition single_word_input_at (m : mem) (bf bw : block) (cursor : Z)
    (payload : int64) : Prop :=
  frame_fields m bf bw 8 cursor /\ 0 <= cursor <= 56 /\
  exists w, Mem.load Mint64 m bw 0 = Some (Vlong w) /\
    Int64.zero_ext 8 (Int64.shru w (Int64.repr (56 - cursor))) =
    Int64.zero_ext 8 payload.

Lemma single_word_input_at_decode m bs bi cursor x :
  single_word_input_at m bs bi cursor (encode_word8 x) ->
  exists w, frame_fields m bs bi 8 cursor /\ 0 <= cursor <= 56 /\
    Mem.load Mint64 m bi 0 = Some (Vlong w) /\
    decode_word8 (Int64.shru w (Int64.repr (56 - cursor))) = x.
Proof.
  intros [HF [HC [w [HW HP]]]].
  exists w. split; [exact HF |]. split; [exact HC |]. split; [exact HW |].
  rewrite <- decode_word8_projection, HP.
  rewrite decode_word8_projection. apply decode_word8_encode.
Qed.

Lemma single_word_input_at_56 m bs bi payload :
  single_word_input m bs bi 8 payload ->
  single_word_input_at m bs bi 56 payload.
Proof.
  intros [HF [HC [w [HW HP]]]].
  split; [exact HF |]. split; [lia |]. exists w. split; [exact HW |].
  change (Int64.repr (56 - 56)) with Int64.zero.
  rewrite Int64.shru_zero. exact HP.
Qed.

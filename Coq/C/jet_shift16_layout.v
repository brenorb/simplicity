(** Complete left/right shift_16 C-to-canonical-Simplicity contracts.
    Initial frames suffice; cursor crossings and arbitrary output contents
    are allowed. Scalar helper calls, writes and cleanup are all discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_shift_wide_exec C.jet_wide C.jet_shift16_layout_machine.
Require Import C.jet_shift16_spec C.jet_shift16_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem shift16_local_spec right :
  jet_local_spec (shift_wide_plain_function W16 right)
    (Ty.Prod (Word 2) (Word 4))
    (Word 4)
    (fun ax => @shift16_plain_spec right Alg.CoreFunSem ax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [amount x]
    HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Ty.Prod (Word 2) (Word 4))))
    with (4 + 16) in * by (destruct right; reflexivity).
  replace (Z.of_nat (bitSize (Word 4)))
    with (16) in * by (destruct right; reflexivity).
  change (frame_input_cells_at m bi edge rc (encode amount ++ encode x)) in Hin.
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize (Word 2))) with 4 in Hin.
  destruct Hin as [Hamount Hinput].
  apply frame_input_word_at_encode in Hamount.
  apply frame_input_word_at_encode in Hinput.
  pose proof (eval_shift16_layout_machine env right m bd dbase bs sbase bi bw edge outedge
    amount x cursor rc HB HA HF ltac:(cbn [wide_bits]; lia) Hamount Hinput Hout) as H.
  rewrite shift16_machine_denotes in H. exact H.
Qed.

Corollary left_shift16_local_spec : jet_local_spec f_simplicity_left_shift_16
  (Ty.Prod (Word 2) (Word 4)) (Word 4)
  (fun ax => @shift16_plain_spec false Alg.CoreFunSem ax).
Proof. exact (shift16_local_spec false). Qed.
Corollary right_shift16_local_spec : jet_local_spec f_simplicity_right_shift_16
  (Ty.Prod (Word 2) (Word 4)) (Word 4)
  (fun ax => @shift16_plain_spec true Alg.CoreFunSem ax).
Proof. exact (shift16_local_spec true). Qed.
Theorem shift16_context right : jet_context_for (shift_wide_plain_function W16 right) (@shift16_plain_spec right).
Proof.
  exact (jet_context _ _ (shift16_plain_spec_parametric right) (shift16_local_spec right)
    ltac:(vm_compute; lia)).
Qed.
Definition shift16_guarantees right := jet_local_spec_guarantees _ _ _ _ (shift16_local_spec right).
Definition shift16_context_guarantees right :=
  jet_context_guarantees _ _ (shift16_plain_spec_parametric right) (shift16_local_spec right)
    ltac:(vm_compute; lia).

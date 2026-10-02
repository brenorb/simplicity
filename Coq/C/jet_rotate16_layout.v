(** Complete left/right rotate_16 C-to-canonical-Simplicity contracts.
    Initial frames suffice; cursor crossings and arbitrary output contents
    are allowed. Scalar helper calls, writes and cleanup are all discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_rotate16_exec C.jet_rotate16_layout_machine.
Require Import C.jet_rotate16_spec C.jet_rotate16_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem rotate16_local_spec right :
  jet_local_spec (rotate16_function right)
    (Ty.Prod (Word 2) (Word (wide_log W16)))
    (Word (wide_log W16))
    (fun ax => @rotate16_spec right Alg.CoreFunSem ax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [amount x]
    HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Ty.Prod (Word 2) (Word (wide_log W16)))))
    with (4 + wide_bits W16) in * by (destruct right; reflexivity).
  replace (Z.of_nat (bitSize (Word (wide_log W16))))
    with (wide_bits W16) in * by (destruct right; reflexivity).
  change (frame_input_cells_at m bi edge rc (encode amount ++ encode x)) in Hin.
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize (Word 2))) with 4 in Hin.
  destruct Hin as [Hamount Hinput].
  apply frame_input_word_at_encode in Hamount.
  apply frame_input_word_at_encode in Hinput.
  pose proof (eval_rotate16_layout_machine env right m bd dbase bs sbase bi bw edge outedge
    amount x cursor rc HB HA HF ltac:(lia) Hamount Hinput Hout) as H.
  rewrite rotate16_machine_denotes in H. exact H.
Qed.

Corollary left_rotate16_local_spec : jet_local_spec f_simplicity_left_rotate_16
  (Ty.Prod (Word 2) (Word 4)) (Word 4)
  (fun ax => @rotate16_spec false Alg.CoreFunSem ax).
Proof. exact (rotate16_local_spec false). Qed.
Corollary right_rotate16_local_spec : jet_local_spec f_simplicity_right_rotate_16
  (Ty.Prod (Word 2) (Word 4)) (Word 4)
  (fun ax => @rotate16_spec true Alg.CoreFunSem ax).
Proof. exact (rotate16_local_spec true). Qed.
Theorem rotate16_context right : jet_context_for (rotate16_function right) (@rotate16_spec right).
Proof.
  exact (jet_context _ _ (rotate16_spec_parametric right) (rotate16_local_spec right)
    ltac:(vm_compute; lia)).
Qed.
Definition rotate16_guarantees right := jet_local_spec_guarantees _ _ _ _ (rotate16_local_spec right).
Definition rotate16_context_guarantees right :=
  jet_context_guarantees _ _ (rotate16_spec_parametric right) (rotate16_local_spec right)
    ltac:(vm_compute; lia).


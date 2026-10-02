(** Complete left/right rotate_8 C-to-canonical-Simplicity contracts.
    Initial frames suffice; cursor crossings and arbitrary output contents
    are allowed. Scalar helper calls, writes and cleanup are all discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_rotate8_exec C.jet_rotate8_layout_machine.
Require Import C.jet_rotate8_spec C.jet_rotate8_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem rotate8_local_spec right :
  jet_local_spec (rotate8_function right)
    (Ty.Prod (Word 2) (Word 3))
    (Word 3)
    (fun ax => @rotate8_spec right Alg.CoreFunSem ax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [amount x]
    HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Ty.Prod (Word 2) (Word 3))))
    with (4 + 8) in * by (destruct right; reflexivity).
  replace (Z.of_nat (bitSize (Word 3)))
    with (8) in * by (destruct right; reflexivity).
  change (frame_input_cells_at m bi edge rc (encode amount ++ encode x)) in Hin.
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize (Word 2))) with 4 in Hin.
  destruct Hin as [Hamount Hinput].
  apply frame_input_word_at_encode in Hamount.
  apply frame_input_word_at_encode in Hinput.
  pose proof (eval_rotate8_layout_machine env right m bd dbase bs sbase bi bw edge outedge
    amount x cursor rc HB HA HF ltac:(lia) Hamount Hinput Hout) as H.
  rewrite rotate8_machine_denotes in H. exact H.
Qed.

Corollary left_rotate8_local_spec : jet_local_spec f_simplicity_left_rotate_8
  (Ty.Prod (Word 2) (Word 3)) (Word 3)
  (fun ax => @rotate8_spec false Alg.CoreFunSem ax).
Proof. exact (rotate8_local_spec false). Qed.
Corollary right_rotate8_local_spec : jet_local_spec f_simplicity_right_rotate_8
  (Ty.Prod (Word 2) (Word 3)) (Word 3)
  (fun ax => @rotate8_spec true Alg.CoreFunSem ax).
Proof. exact (rotate8_local_spec true). Qed.
Theorem rotate8_context right : jet_context_for (rotate8_function right) (@rotate8_spec right).
Proof.
  exact (jet_context _ _ (rotate8_spec_parametric right) (rotate8_local_spec right)
    ltac:(vm_compute; lia)).
Qed.
Definition rotate8_guarantees right := jet_local_spec_guarantees _ _ _ _ (rotate8_local_spec right).
Definition rotate8_context_guarantees right :=
  jet_context_guarantees _ _ (rotate8_spec_parametric right) (rotate8_local_spec right)
    ltac:(vm_compute; lia).

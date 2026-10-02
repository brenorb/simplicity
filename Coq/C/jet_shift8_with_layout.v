(** Complete fill-controlled byte shift C-to-canonical-Simplicity contracts.
    All execution/value premises are discharged from API-valid initial frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_shift8_with_exec C.jet_shift8_with_layout_machine.
Require Import C.jet_shift8_with_spec C.jet_shift8_with_denotes.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem shift8_with_local_spec right :
  jet_local_spec (shift8_with_function right)
    (Ty.Prod Bit (Ty.Prod (Word 2) (Word 3))) (Word 3)
    (fun fax => @shift8_with_spec right Alg.CoreFunSem fax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [fill [amount x]]
    HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Ty.Prod (Word 2) (Word 3))))) with 13 in *.
  change (Z.of_nat (bitSize (Word 3))) with 8 in *.
  change (frame_input_cells_at m bi edge rc (encode fill ++ (encode amount ++ encode x))) in Hin.
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize Bit)) with 1 in Hin.
  destruct Hin as [Hfill Hin].
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize (Word 2))) with 4 in Hin.
  destruct Hin as [Hamount Hinput].
  apply frame_input_word_at_encode in Hamount.
  apply frame_input_word_at_encode in Hinput.
  assert (HfillBit : frame_input_bit_at m bi edge rc (Bit.toBool fill)).
  { specialize (Hfill 0%nat (Some (Bit.toBool fill))
      ltac:(destruct fill as [[]|[]]; reflexivity)).
    change (frame_input_bit_at m bi edge (rc + 0) (Bit.toBool fill)) in Hfill.
    rewrite Z.add_0_r in Hfill; exact Hfill. }
  replace (rc + 1 + 4) with (rc + (1 + 4)) in Hinput by lia.
  pose proof (eval_shift8_with_layout_machine env right m bd dbase bs sbase bi bw edge outedge
    fill amount x cursor rc HB HA HF ltac:(lia) HfillBit Hamount Hinput Hout) as H.
  rewrite shift8_with_machine_denotes in H. exact H.
Qed.

Corollary left_shift_with8_local_spec : jet_local_spec f_simplicity_left_shift_with_8
  (Ty.Prod Bit (Ty.Prod (Word 2) (Word 3))) (Word 3)
  (fun fax => @shift8_with_spec Datatypes.false Alg.CoreFunSem fax).
Proof. exact (shift8_with_local_spec Datatypes.false). Qed.
Corollary right_shift_with8_local_spec : jet_local_spec f_simplicity_right_shift_with_8
  (Ty.Prod Bit (Ty.Prod (Word 2) (Word 3))) (Word 3)
  (fun fax => @shift8_with_spec Datatypes.true Alg.CoreFunSem fax).
Proof. exact (shift8_with_local_spec Datatypes.true). Qed.
Theorem shift8_with_context right : jet_context_for (shift8_with_function right) (@shift8_with_spec right).
Proof.
  exact (jet_context _ _ (shift8_with_spec_parametric right) (shift8_with_local_spec right)
    ltac:(vm_compute; lia)).
Qed.
Definition shift8_with_guarantees right :=
  jet_local_spec_guarantees _ _ _ _ (shift8_with_local_spec right).
Definition shift8_with_context_guarantees right :=
  jet_context_guarantees _ _ (shift8_with_spec_parametric right) (shift8_with_local_spec right)
    ltac:(vm_compute; lia).

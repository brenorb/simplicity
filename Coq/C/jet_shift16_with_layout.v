(** Complete fill-controlled 16-bit shift C-to-canonical-Simplicity contracts.
    All execution/value premises are discharged from API-valid initial frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_shift_wide_with_exec C.jet_shift16_with_layout_machine.
Require Import C.jet_shift_wide_helper_exec.
Require Import C.jet_shift16_with_spec C.jet_shift16_with_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift16_with_machine_denotes right fill amount x :
  shift16_with_machine_value right fill amount x =
    @shift16_with_spec right Alg.CoreFunSem (fill,(amount,x)).
Proof.
  assert (HR : Int64.unsigned (Int64.repr (@toZ (WordToZ 4) x)) = @toZ (WordToZ 4) x).
  { apply Int64.unsigned_repr. pose proof (word_toZ_range 4 x) as H.
    change (0 <= @toZ (WordToZ 4) x < 65536) in H.
    change Int64.max_unsigned with 18446744073709551615; lia. }
  assert (HA : Int.unsigned (Int.repr (@toZ (WordToZ 2) amount)) = @toZ (WordToZ 2) amount).
  { apply Int.unsigned_repr. pose proof (word_toZ_range 2 amount) as H.
    change (0 <= @toZ (WordToZ 2) amount < 16) in H.
    change Int.max_unsigned with 4294967295; lia. }
  assert (HF : Bit.fromBool (Bit.toBool fill) = fill) by (destruct fill as [[]|[]]; reflexivity).
  unfold shift16_with_machine_value.
  change (decode_wide W16 (Int64.zero_ext 16
    (shift_wide_payload W16 right (Bit.toBool fill) (Int64.repr (@toZ (WordToZ 4) x))
      (Int.repr (@toZ (WordToZ 2) amount)))) =
      @shift16_with_spec right Alg.CoreFunSem (fill,(amount,x))).
  rewrite (shift16_with_payload_denotes right (Bit.toBool fill) amount x _ _ HR HA), HF.
  reflexivity.
Qed.

Theorem shift16_with_local_spec right :
  jet_local_spec (shift_wide_with_function W16 right)
    (Ty.Prod Bit (Ty.Prod (Word 2) (Word 4))) (Word 4)
    (fun fax => @shift16_with_spec right Alg.CoreFunSem fax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [fill [amount x]]
    HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Ty.Prod (Word 2) (Word 4))))) with 21 in *.
  change (Z.of_nat (bitSize (Word 4))) with 16 in *.
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
  pose proof (eval_shift16_with_layout_machine env right m bd dbase bs sbase bi bw edge outedge
    fill amount x cursor rc HB HA HF ltac:(cbn [wide_bits]; lia) HfillBit Hamount Hinput Hout) as H.
  rewrite shift16_with_machine_denotes in H. exact H.
Qed.

Corollary left_shift_with16_local_spec : jet_local_spec f_simplicity_left_shift_with_16
  (Ty.Prod Bit (Ty.Prod (Word 2) (Word 4))) (Word 4)
  (fun fax => @shift16_with_spec Datatypes.false Alg.CoreFunSem fax).
Proof. exact (shift16_with_local_spec Datatypes.false). Qed.
Corollary right_shift_with16_local_spec : jet_local_spec f_simplicity_right_shift_with_16
  (Ty.Prod Bit (Ty.Prod (Word 2) (Word 4))) (Word 4)
  (fun fax => @shift16_with_spec Datatypes.true Alg.CoreFunSem fax).
Proof. exact (shift16_with_local_spec Datatypes.true). Qed.
Theorem shift16_with_context right : jet_context_for (shift_wide_with_function W16 right) (@shift16_with_spec right).
Proof.
  exact (jet_context _ _ (shift16_with_spec_parametric right) (shift16_with_local_spec right)
    ltac:(vm_compute; lia)).
Qed.
Definition shift16_with_guarantees right :=
  jet_local_spec_guarantees _ _ _ _ (shift16_with_local_spec right).
Definition shift16_with_context_guarantees right :=
  jet_context_guarantees _ _ (shift16_with_spec_parametric right) (shift16_with_local_spec right)
    ltac:(vm_compute; lia).

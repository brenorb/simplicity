(** Complete fill-controlled 64-bit shift C-to-canonical-Simplicity contracts.
    All execution/value premises are discharged from API-valid initial frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_shift_wide_with_exec C.jet_shift_byte_with_layout_machine C.jet_left_rotate_wide_exec.
Require Import C.jet_shift_wide_helper_exec.
Require Import C.jet_shift64_with_spec C.jet_shift64_with_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift64_with_machine_denotes right fill amount x :
  shift_byte_with_machine_value R64 right fill amount x =
    @shift64_with_spec right Alg.CoreFunSem (fill,(amount,x)).
Proof.
  assert (HR : Int64.unsigned (Int64.repr (@toZ (WordToZ 6) x)) = @toZ (WordToZ 6) x).
  { apply Int64.unsigned_repr. pose proof (word_toZ_range 6 x) as H.
    change (0 <= @toZ (WordToZ 6) x < 18446744073709551616) in H.
    change Int64.max_unsigned with 18446744073709551615; lia. }
  assert (HA : Int.unsigned (Int.repr (@toZ (WordToZ 3) amount)) = @toZ (WordToZ 3) amount).
  { apply Int.unsigned_repr. pose proof (word_toZ_range 3 amount) as H.
    change (0 <= @toZ (WordToZ 3) amount < 256) in H.
    change Int.max_unsigned with 4294967295; lia. }
  assert (HF : Bit.fromBool (Bit.toBool fill) = fill) by (destruct fill as [[]|[]]; reflexivity).
  unfold shift_byte_with_machine_value.
  change (decode_wide W64 (Int64.zero_ext 64
    (shift_wide_payload W64 right (Bit.toBool fill) (Int64.repr (@toZ (WordToZ 6) x))
      (Int.repr (@toZ (WordToZ 3) amount)))) =
      @shift64_with_spec right Alg.CoreFunSem (fill,(amount,x))).
  rewrite (shift64_with_payload_denotes right (Bit.toBool fill) amount x _ _ HR HA), HF.
  reflexivity.
Qed.

Theorem shift64_with_local_spec right :
  jet_local_spec (shift_wide_with_function W64 right)
    (Ty.Prod Bit (Ty.Prod (Word 3) (Word 6))) (Word 6)
    (fun fax => @shift64_with_spec right Alg.CoreFunSem fax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [fill [amount x]]
    HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Ty.Prod (Word 3) (Word 6))))) with 73 in *.
  change (Z.of_nat (bitSize (Word 6))) with 64 in *.
  change (frame_input_cells_at m bi edge rc (encode fill ++ (encode amount ++ encode x))) in Hin.
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize Bit)) with 1 in Hin.
  destruct Hin as [Hfill Hin].
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize (Word 3))) with 8 in Hin.
  destruct Hin as [Hamount Hinput].
  apply frame_input_word_at_encode in Hamount.
  apply frame_input_word_at_encode in Hinput.
  assert (HfillBit : frame_input_bit_at m bi edge rc (Bit.toBool fill)).
  { specialize (Hfill 0%nat (Some (Bit.toBool fill))
      ltac:(destruct fill as [[]|[]]; reflexivity)).
    change (frame_input_bit_at m bi edge (rc + 0) (Bit.toBool fill)) in Hfill.
    rewrite Z.add_0_r in Hfill; exact Hfill. }
  replace (rc + 1 + 8) with (rc + (1 + 8)) in Hinput by lia.
  pose proof (eval_shift_byte_with_layout_machine env R64 right m bd dbase bs sbase bi bw edge outedge
    fill amount x cursor rc HB HA HF ltac:(cbn [byte_rotate_width wide_bits]; lia) HfillBit Hamount Hinput Hout) as H.
  rewrite shift64_with_machine_denotes in H. exact H.
Qed.

Corollary left_shift_with64_local_spec : jet_local_spec f_simplicity_left_shift_with_64
  (Ty.Prod Bit (Ty.Prod (Word 3) (Word 6))) (Word 6)
  (fun fax => @shift64_with_spec Datatypes.false Alg.CoreFunSem fax).
Proof. exact (shift64_with_local_spec Datatypes.false). Qed.
Corollary right_shift_with64_local_spec : jet_local_spec f_simplicity_right_shift_with_64
  (Ty.Prod Bit (Ty.Prod (Word 3) (Word 6))) (Word 6)
  (fun fax => @shift64_with_spec Datatypes.true Alg.CoreFunSem fax).
Proof. exact (shift64_with_local_spec Datatypes.true). Qed.
Theorem shift64_with_context right : jet_context_for (shift_wide_with_function W64 right) (@shift64_with_spec right).
Proof.
  exact (jet_context _ _ (shift64_with_spec_parametric right) (shift64_with_local_spec right)
    ltac:(vm_compute; lia)).
Qed.
Definition shift64_with_guarantees right :=
  jet_local_spec_guarantees _ _ _ _ (shift64_with_local_spec right).
Definition shift64_with_context_guarantees right :=
  jet_context_guarantees _ _ (shift64_with_spec_parametric right) (shift64_with_local_spec right)
    ltac:(vm_compute; lia).

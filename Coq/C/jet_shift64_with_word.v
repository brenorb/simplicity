(** Low-bit fill-controlled 64-bit carrier bridge. The C helper's left-shift
    high bits need not be zero; the actual writer retains only the low word. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_rotate_count_exec C.jet_rotate_control_word.
Require Import C.jet_shift_wide_helper_exec C.jet_shift_wide_bits C.jet_shift_wide_fill_word.
Require Import C.jet_shift64_spec C.jet_shift64_with_spec C.jet_complement_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift64_with_payload_bits right fill amount (x : Ty.tySem (Word 6)) r a j :
  Int64.unsigned r = @toZ (WordToZ 6) x -> Int.unsigned a = @toZ (WordToZ 3) amount ->
  0 <= j < 64 ->
  Int64.testbit (shift_wide_payload W64 right fill r a) j =
    Z.testbit (@toZ (WordToZ 6)
      (@shift64_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)))) j.
Proof.
  intros HR HA Hj.
  assert (HAC : Int.zero_ext 8 a = a).
  { apply byte_carrier_cast_id. rewrite HA.
    pose proof (word_toZ_range 3 amount) as H.
    change (0 <= @toZ (WordToZ 3) amount < 256) in H; lia. }
  rewrite shift64_with_complement_normalform.
  unfold shift_wide_payload. rewrite HAC. destruct fill; cbn [shift_wide_maybe_fill].
  - rewrite shift_wide_fill_result_bits by exact Hj.
    rewrite (@shift_wide_count_result_bits W64 right (@complement_spec 6 Alg.CoreFunSem x)) by
      (try exact Hj; apply shift_wide_fill_result_unsigned; exact HR).
    change (negb (Z.testbit (@toZ (WordToZ 6) (@complement_spec 6 Alg.CoreFunSem x))
      (j - rotate_signed_amount right (Int.unsigned a))) =
      Z.testbit (@toZ (WordToZ 6) (@complement_spec 6 Alg.CoreFunSem
        (@shift64_plain_spec right Alg.CoreFunSem (amount,@complement_spec 6 Alg.CoreFunSem x)))) j).
    rewrite (complement_spec_bits 6
      (@shift64_plain_spec right Alg.CoreFunSem (amount,@complement_spec 6 Alg.CoreFunSem x)) j Hj).
    rewrite shift64_plain_spec_bits by exact Hj. rewrite HA; reflexivity.
  - rewrite (@shift_wide_count_result_bits W64 right x) by assumption.
    rewrite shift64_plain_spec_bits by exact Hj. rewrite HA; reflexivity.
Qed.

Lemma shift64_with_payload_denotes right fill amount (x : Ty.tySem (Word 6)) r a :
  Int64.unsigned r = @toZ (WordToZ 6) x -> Int.unsigned a = @toZ (WordToZ 3) amount ->
  decode_wide W64 (Int64.zero_ext 64 (shift_wide_payload W64 right fill r a)) =
    @shift64_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)).
Proof.
  intros HR HA. unfold decode_wide. apply word_fromZ_bits. intros j Hj.
  change (0 <= j < 64) in Hj.
  change (Int64.testbit (Int64.zero_ext 64 (shift_wide_payload W64 right fill r a)) j =
    Z.testbit (@toZ (WordToZ 6)
      (@shift64_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)))) j).
  rewrite Int64.bits_zero_ext, (zlt_true _ j 64) by lia.
  apply shift64_with_payload_bits; assumption.
Qed.

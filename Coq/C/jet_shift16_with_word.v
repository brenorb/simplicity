(** Low-bit fill-controlled 16-bit carrier bridge. The C helper's left-shift
    high bits need not be zero; the actual writer retains only the low word. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_rotate_count_exec C.jet_rotate_control_word.
Require Import C.jet_shift_wide_helper_exec C.jet_shift_wide_bits C.jet_shift_wide_fill_word.
Require Import C.jet_shift16_spec C.jet_shift16_with_spec C.jet_complement_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift16_with_payload_bits right fill amount (x : Ty.tySem (Word 4)) r a j :
  Int64.unsigned r = @toZ (WordToZ 4) x -> Int.unsigned a = @toZ (WordToZ 2) amount ->
  0 <= j < 16 ->
  Int64.testbit (shift_wide_payload W16 right fill r a) j =
    Z.testbit (@toZ (WordToZ 4)
      (@shift16_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)))) j.
Proof.
  intros HR HA Hj.
  assert (HAC : Int.zero_ext 8 a = a).
  { apply byte_carrier_cast_id. rewrite HA.
    pose proof (word_toZ_range 2 amount) as H.
    change (0 <= @toZ (WordToZ 2) amount < 16) in H; lia. }
  rewrite shift16_with_complement_normalform.
  unfold shift_wide_payload. rewrite HAC. destruct fill; cbn [shift_wide_maybe_fill].
  - rewrite shift_wide_fill_result_bits by exact Hj.
    rewrite (@shift_wide_count_result_bits W16 right (@complement_spec 4 Alg.CoreFunSem x)) by
      (try exact Hj; apply shift_wide_fill_result_unsigned; exact HR).
    change (negb (Z.testbit (@toZ (WordToZ 4) (@complement_spec 4 Alg.CoreFunSem x))
      (j - rotate_signed_amount right (Int.unsigned a))) =
      Z.testbit (@toZ (WordToZ 4) (@complement_spec 4 Alg.CoreFunSem
        (@shift16_plain_spec right Alg.CoreFunSem (amount,@complement_spec 4 Alg.CoreFunSem x)))) j).
    rewrite (complement_spec_bits 4
      (@shift16_plain_spec right Alg.CoreFunSem (amount,@complement_spec 4 Alg.CoreFunSem x)) j Hj).
    rewrite shift16_plain_spec_bits by exact Hj. rewrite HA; reflexivity.
  - rewrite (@shift_wide_count_result_bits W16 right x) by assumption.
    rewrite shift16_plain_spec_bits by exact Hj. rewrite HA; reflexivity.
Qed.

Lemma shift16_with_payload_denotes right fill amount (x : Ty.tySem (Word 4)) r a :
  Int64.unsigned r = @toZ (WordToZ 4) x -> Int.unsigned a = @toZ (WordToZ 2) amount ->
  decode_wide W16 (Int64.zero_ext 16 (shift_wide_payload W16 right fill r a)) =
    @shift16_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)).
Proof.
  intros HR HA. unfold decode_wide. apply word_fromZ_bits. intros j Hj.
  change (0 <= j < 16) in Hj.
  change (Int64.testbit (Int64.zero_ext 16 (shift_wide_payload W16 right fill r a)) j =
    Z.testbit (@toZ (WordToZ 4)
      (@shift16_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)))) j).
  rewrite Int64.bits_zero_ext, (zlt_true _ j 16) by lia.
  apply shift16_with_payload_bits; assumption.
Qed.

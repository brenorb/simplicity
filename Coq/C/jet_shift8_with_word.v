(** Exact C carrier bridge for literal fill-input byte shift specifications.
    Exact representation, rather than equality after decoding, is needed for
    the helper's second fill XOR. Payload values remain symbolic. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_word_repr C.jet_rotate_count_exec.
Require Import C.jet_shift8_expr C.jet_shift8_helper_exec C.jet_shift8_word.
Require Import C.jet_shift8_spec C.jet_shift8_fill_word C.jet_shift8_with_spec.
Require Import C.jet_complement_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift8_count_result_repr right amount (x : Ty.tySem (Word 3)) r a :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  Int.unsigned a = @toZ (WordToZ 2) amount ->
  shift8_count_result right r a =
    Int.repr (@toZ (WordToZ 3) (@shift8_plain_spec right Alg.CoreFunSem (amount,x))).
Proof.
  intros HR HA. apply Int.same_bits_eq. intros j Hj.
  change (0 <= j < 32) in Hj. rewrite Int.testbit_repr by exact Hj.
  destruct (Z_lt_ge_dec j 8) as [HL|HH].
  - rewrite (@shift8_count_result_bits right x) by (assumption || lia).
    rewrite HA. symmetry. apply shift8_plain_spec_bits; lia.
  - unfold shift8_count_result. destruct (zlt (Int.unsigned a) 8).
    + unfold shift8_scalar_result. rewrite Int.bits_zero_ext, (zlt_false _ j 8) by lia.
      symmetry. apply word_toZ_high_bits. change (8 <= j); lia.
    + rewrite Int.bits_zero. symmetry. apply word_toZ_high_bits. change (8 <= j); lia.
Qed.

Lemma shift8_count_result_unsigned right amount (x : Ty.tySem (Word 3)) r a :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  Int.unsigned a = @toZ (WordToZ 2) amount ->
  Int.unsigned (shift8_count_result right r a) =
    @toZ (WordToZ 3) (@shift8_plain_spec right Alg.CoreFunSem (amount,x)).
Proof.
  intros HR HA. rewrite (shift8_count_result_repr right amount x r a HR HA).
  apply Int.unsigned_repr.
  pose proof (word_toZ_range 3 (@shift8_plain_spec right Alg.CoreFunSem (amount,x))) as H.
  change (0 <= @toZ (WordToZ 3) (@shift8_plain_spec right Alg.CoreFunSem (amount,x)) < 256) in H.
  change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma shift8_with_payload_repr right fill amount (x : Ty.tySem (Word 3)) r a :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  Int.unsigned a = @toZ (WordToZ 2) amount ->
  shift8_payload right fill r a =
    Int.repr (@toZ (WordToZ 3)
      (@shift8_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)))).
Proof.
  intros HR HA.
  assert (HRC : Int.zero_ext 8 r = r).
  { apply byte_carrier_cast_id. rewrite HR.
    pose proof (word_toZ_range 3 x) as H. exact H. }
  assert (HAC : Int.zero_ext 8 a = a).
  { apply byte_carrier_cast_id. rewrite HA.
    pose proof (word_toZ_range 2 amount) as H.
    change (0 <= @toZ (WordToZ 2) amount < 16) in H; lia. }
  rewrite shift8_with_complement_normalform.
  unfold shift8_payload. rewrite HRC, HAC.
  destruct fill; cbn [shift8_maybe_fill].
  - apply shift8_fill_result_repr. apply shift8_count_result_unsigned; [|exact HA].
    apply shift8_fill_result_unsigned; exact HR.
  - apply shift8_count_result_repr; assumption.
Qed.

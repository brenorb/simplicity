(** Symbolic bridge from the actual promoted byte shift/count branch to the
    literal canonical variable-control shift program. No count modulo is used. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_spec C.jet_word_repr C.jet_rotate_count_exec C.jet_rotate_control_word.
Require Import C.jet_shift8_expr C.jet_shift8_helper_exec C.jet_shift8_layout_machine C.jet_shift8_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift8_count_result_bits right (x : Ty.tySem (Word 3)) r a j :
  Int.unsigned r = @toZ (WordToZ 3) x -> 0 <= j < 8 ->
  Int.testbit (shift8_count_result right r a) j =
    Z.testbit (@toZ (WordToZ 3) x) (j - rotate_signed_amount right (Int.unsigned a)).
Proof.
  intros HR Hj. pose proof (Int.unsigned_range a) as HA.
  unfold shift8_count_result. destruct (zlt (Int.unsigned a) 8) as [HL|HG].
  - unfold shift8_scalar_result. rewrite Int.bits_zero_ext, (zlt_true _ j 8) by lia.
    destruct right; cbn [rotate_signed_amount].
    + rewrite Int.bits_shr by (change Int.zwordsize with 32; lia).
      rewrite (zlt_true _ (j + Int.unsigned a) Int.zwordsize) by
        (change Int.zwordsize with 32; lia).
      unfold Int.testbit. rewrite HR. f_equal; lia.
    + rewrite Int.bits_shl by (change Int.zwordsize with 32; lia).
      destruct (zlt j (Int.unsigned a)) as [Hsmall|Hlarge].
      * symmetry. apply Z.testbit_neg_r; lia.
      * unfold Int.testbit. rewrite HR. reflexivity.
  - rewrite Int.bits_zero. destruct right; cbn [rotate_signed_amount].
    + symmetry. apply word_toZ_high_bits. change (8 <= j - -Int.unsigned a); lia.
    + symmetry. apply Z.testbit_neg_r; lia.
Qed.

Lemma shift8_machine_denotes right amount x :
  shift8_machine_value right amount x = @shift8_plain_spec right Alg.CoreFunSem (amount,x).
Proof.
  pose proof (word_toZ_range 2 amount) as HA. change (0 <= @toZ (WordToZ 2) amount < 16) in HA.
  pose proof (word_toZ_range 3 x) as HX. change (0 <= @toZ (WordToZ 3) x < 256) in HX.
  assert (HU : Int.unsigned (Int.repr (@toZ (WordToZ 2) amount)) = @toZ (WordToZ 2) amount).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  assert (HR : Int.unsigned (Int.repr (@toZ (WordToZ 3) x)) = @toZ (WordToZ 3) x).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  assert (HAC : Int.zero_ext 8 (Int.repr (@toZ (WordToZ 2) amount)) = Int.repr (@toZ (WordToZ 2) amount)).
  { apply byte_carrier_cast_id. rewrite HU; lia. }
  assert (HRC : Int.zero_ext 8 (Int.repr (@toZ (WordToZ 3) x)) = Int.repr (@toZ (WordToZ 3) x)).
  { apply byte_carrier_cast_id. rewrite HR; exact HX. }
  unfold shift8_machine_value, decode_word8.
  rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2
      (Int.zero_ext 8 (shift8_payload right false (Int.repr (@toZ (WordToZ 3) x))
        (Int.repr (@toZ (WordToZ 2) amount)))));
     change Int.max_unsigned with 4294967295 in *;
     change Int64.max_unsigned with 18446744073709551615; lia).
  apply (proj2 (word_fromZ_bits 3 (@shift8_plain_spec right Alg.CoreFunSem (amount,x)) _)).
  intros j Hj. change (0 <= j < 8) in Hj.
  change (Int.testbit (Int.zero_ext 8 (shift8_payload right false (Int.repr (@toZ (WordToZ 3) x))
    (Int.repr (@toZ (WordToZ 2) amount)))) j =
    Z.testbit (@toZ (WordToZ 3) (@shift8_plain_spec right Alg.CoreFunSem (amount,x))) j).
  rewrite Int.bits_zero_ext, (zlt_true _ j 8) by lia.
  unfold shift8_payload, shift8_maybe_fill. rewrite HRC, HAC.
  rewrite (@shift8_count_result_bits right x) by assumption.
  rewrite HU. symmetry. apply shift8_plain_spec_bits; exact Hj.
Qed.

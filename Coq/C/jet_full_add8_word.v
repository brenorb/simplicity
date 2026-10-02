(** Symbolic carry-input byte addition, retaining the C short-circuit carry. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_readBit_layout C.jet_add8 C.jet_add8_word.
Require Import C.jet_full_increment8_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_add8_spec {term : Alg.Core.Algebra} := @Word.fullAdder 3 term.
Definition full_add8_first_carry r t :=
  Int.ltu (Int.sub (Int.repr 255) (add8_u t)) (add8_u r).
Definition full_add8_second_carry cin r t :=
  Int.ltu (Int.sub (Int.repr 255) (bit_int cin)) (add8_sum_raw r t).
Definition full_add8_carry cin r t :=
  orb (full_add8_first_carry r t) (full_add8_second_carry cin r t).
Definition full_add8_raw cin r t := Int.add (add8_sum_raw r t) (bit_int cin).
Definition full_add8_payload cin r t := Int.zero_ext 8 (full_add8_raw cin r t).

Lemma add8_sum_raw_unsigned r t :
  Int.unsigned (add8_sum_raw r t) = Int.unsigned (add8_u r) + Int.unsigned (add8_u t).
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range t) as HT.
  unfold add8_sum_raw. rewrite Int.mul_commut, Int.mul_one. unfold Int.add.
  apply Int.unsigned_repr. change Int.max_unsigned with 4294967295. lia.
Qed.
Lemma full_add8_payload_unsigned cin r t :
  Int.unsigned (full_add8_payload cin r t) =
    (Int.unsigned (add8_u r) + Int.unsigned (add8_u t) + Int.unsigned (bit_int cin)) mod 256.
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range t) as HT.
  assert (HC : 0 <= Int.unsigned (bit_int cin) <= 1).
  { destruct cin; [change (0 <= 1 <= 1)|change (0 <= 0 <= 1)]; lia. }
  unfold full_add8_payload, full_add8_raw.
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  unfold Int.add. rewrite Int.unsigned_repr by
    (rewrite add8_sum_raw_unsigned; change Int.max_unsigned with 4294967295; lia).
  rewrite add8_sum_raw_unsigned. reflexivity.
Qed.
Lemma full_add8_second_overflow cin r t :
  full_add8_second_carry cin r t =
    (255 <? Int.unsigned (add8_u r) + Int.unsigned (add8_u t) + Int.unsigned (bit_int cin)).
Proof.
  assert (HC : 0 <= Int.unsigned (bit_int cin) <= 1).
  { destruct cin; [change (0 <= 1 <= 1)|change (0 <= 0 <= 1)]; lia. }
  unfold full_add8_second_carry, Int.sub, Int.ltu.
  change (Int.unsigned (Int.repr 255)) with 255.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  rewrite add8_sum_raw_unsigned.
  destruct (zlt (255 - Int.unsigned (bit_int cin))
    (Int.unsigned (add8_u r) + Int.unsigned (add8_u t)));
    symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma full_add8_overflow cin r t :
  full_add8_carry cin r t =
    (255 <? Int.unsigned (add8_u r) + Int.unsigned (add8_u t) + Int.unsigned (bit_int cin)).
Proof.
  unfold full_add8_carry, full_add8_first_carry.
  rewrite add8_overflow, full_add8_second_overflow.
  pose proof (Int.unsigned_range (bit_int cin)) as HC.
  destruct (255 <? Int.unsigned (add8_u r) + Int.unsigned (add8_u t)) eqn:Hfirst.
  - apply Z.ltb_lt in Hfirst. cbn. symmetry. apply Z.ltb_lt. lia.
  - reflexivity.
Qed.
Lemma full_add8_values_denote_spec (c : Ty.tySem Bit) left right :
  ((if full_add8_carry (Bit.toBool c) (read8_result left) (read8_result right)
    then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned
      (full_add8_payload (Bit.toBool c) (read8_result left) (read8_result right))))) =
    @full_add8_spec Alg.CoreFunSem (c, (decode_word8 left, decode_word8 right)).
Proof.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 3))).
  unfold full_add8_spec. rewrite Word.fullAdder_correct, (@toZ_Pair BitToZ (WordToZ 3)).
  rewrite full_add8_overflow, decode_word8_of_int, full_add8_payload_unsigned, !read8_result_unsigned.
  assert (Hbit : Int.unsigned (bit_int (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  rewrite Hbit.
  set (a := @toZ (WordToZ 3) (decode_word8 left)).
  set (b := @toZ (WordToZ 3) (decode_word8 right)).
  set (cin := @toZ BitToZ c).
  assert (HA : 0 <= a < 256).
  { unfold a, decode_word8. rewrite to_fromZ. apply Z.mod_pos_bound. lia. }
  assert (HB : 0 <= b < 256).
  { unfold b, decode_word8. rewrite to_fromZ. apply Z.mod_pos_bound. lia. }
  assert (HC : 0 <= cin <= 1) by (unfold cin; destruct c as [[]|[]]; cbn; lia).
  change (@toZ BitToZ (if 255 <? a + b + cin then inr tt else inl tt) * 256 +
    ((a + b + cin) mod 256) mod 256 = a + b + cin).
  rewrite Z.mod_mod by lia. destruct (255 <? a + b + cin) eqn:Hcarry.
  - apply Z.ltb_lt in Hcarry.
    change (1 * 256 + (a + b + cin) mod 256 = a + b + cin).
    replace ((a + b + cin) mod 256) with (a + b + cin - 256); [lia|].
    apply Z.mod_unique with (q := 1); lia.
  - apply Z.ltb_ge in Hcarry.
    change (0 * 256 + (a + b + cin) mod 256 = a + b + cin).
    rewrite Z.mod_small by lia. lia.
Qed.
Lemma full_add8_spec_parametric : Alg.Core.Parametric (@full_add8_spec).
Proof. intros alg1 alg2 R. apply Word.fullAdder_Parametric. Qed.

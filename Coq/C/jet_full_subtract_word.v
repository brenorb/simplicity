(** Shared borrow-input subtraction representation, including both carrier wraps. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_add8 C.jet_add8_word C.jet_readBit_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_toZ C.jet_predicate_spec.
Require Import C.jet_subtract_spec C.jet_subtract_word C.jet_full_increment8_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_subtract8_first_borrow r t := Int.ltu (add8_u r) (add8_u t).
Definition full_subtract8_diff r t := Int.sub (Int.mul Int.one (add8_u r)) (add8_u t).
Definition full_subtract8_second_borrow cin r t := Int.ltu (full_subtract8_diff r t) (bit_int cin).
Definition full_subtract8_borrow cin r t :=
  orb (full_subtract8_first_borrow r t) (full_subtract8_second_borrow cin r t).
Definition full_subtract8_raw cin r t := Int.sub (full_subtract8_diff r t) (bit_int cin).
Definition full_subtract8_payload cin r t := Int.zero_ext 8 (full_subtract8_raw cin r t).
Definition wide_full_subtract_first_borrow r t := Int64.ltu r t.
Definition wide_full_subtract_second_borrow cin r t := Int64.ltu (Int64.sub r t) (bit_long cin).
Definition wide_full_subtract_borrow cin r t :=
  orb (wide_full_subtract_first_borrow r t) (wide_full_subtract_second_borrow cin r t).
Definition wide_full_subtract_payload cin r t := Int64.sub (Int64.sub r t) (bit_long cin).

Lemma full_subtract_representation_matches n (c : Ty.tySem Bit) (x y payload : Ty.tySem (Word n)) :
  @toZ (WordToZ n) payload =
    (@toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c) mod word_modulus n ->
  ((if @toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c <? 0
      then inr tt else inl tt), payload) = @full_subtract_word_spec Alg.CoreFunSem n (c, (x, y)).
Proof.
  intros HP. apply borrow_word_balance_injective. rewrite full_subtract_word_spec_numeric.
  pose proof (word_value_bounds n x) as HX. pose proof (word_value_bounds n y) as HY.
  pose proof (word_modulus_positive n) as HM.
  assert (HC : 0 <= @toZ BitToZ c <= 1) by (destruct c as [[]|[]]; cbn; lia).
  pose proof (borrow_mod_balance (word_modulus n)
    (@toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c) HM ltac:(lia)) as HB.
  unfold borrow_word_balance. cbn [fst snd]. rewrite HP.
  destruct (@toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c <? 0); exact HB.
Qed.
Lemma borrow_short_circuit a b c : 0 <= c ->
  orb (a <? b) (a - b <? c) = (a - b - c <? 0).
Proof.
  intros HC. destruct (a <? b) eqn:HF.
  - apply Z.ltb_lt in HF. cbn [orb]. symmetry. apply Z.ltb_lt. lia.
  - cbn [orb]. apply borrow_less_difference.
Qed.
Lemma carrier_mod_difference_word n carrier a b : 0 < carrier -> (word_modulus n | carrier) ->
  (a mod carrier - b) mod word_modulus n = (a - b) mod word_modulus n.
Proof.
  intros HC HD. rewrite <- (Zminus_mod_idemp_l (a mod carrier) b (word_modulus n)).
  rewrite carrier_mod_word by assumption. apply Zminus_mod_idemp_l.
Qed.
Lemma full_subtract8_first_borrow_numeric r t :
  full_subtract8_first_borrow r t = (Int.unsigned (add8_u r) <? Int.unsigned (add8_u t)).
Proof.
  unfold full_subtract8_first_borrow, Int.ltu.
  destruct (zlt (Int.unsigned (add8_u r)) (Int.unsigned (add8_u t)));
    symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma full_subtract8_borrow_numeric cin r t :
  full_subtract8_borrow cin r t =
    (Int.unsigned (add8_u r) - Int.unsigned (add8_u t) - Int.unsigned (bit_int cin) <? 0).
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range t) as HT.
  pose proof (Int.unsigned_range (bit_int cin)) as HC.
  unfold full_subtract8_borrow. rewrite full_subtract8_first_borrow_numeric.
  destruct (Int.unsigned (add8_u r) <? Int.unsigned (add8_u t)) eqn:HF.
  - apply Z.ltb_lt in HF. cbn [orb]. symmetry. apply Z.ltb_lt. lia.
  - apply Z.ltb_ge in HF. cbn [orb].
    unfold full_subtract8_second_borrow, full_subtract8_diff.
    rewrite Int.mul_commut, Int.mul_one. unfold Int.sub, Int.ltu.
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    destruct (zlt (Int.unsigned (add8_u r) - Int.unsigned (add8_u t)) (Int.unsigned (bit_int cin)));
      symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma full_subtract8_payload_numeric cin r t :
  @toZ (WordToZ 3) (decode_word8 (Int64.repr (Int.unsigned (full_subtract8_payload cin r t)))) =
    (Int.unsigned (add8_u r) - Int.unsigned (add8_u t) - Int.unsigned (bit_int cin)) mod word_modulus 3.
Proof.
  rewrite decode_word8_of_int. unfold full_subtract8_payload.
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia). rewrite Z.mod_mod by lia.
  unfold full_subtract8_raw, full_subtract8_diff. rewrite Int.mul_commut, Int.mul_one.
  unfold Int.sub. rewrite !Int.unsigned_repr_eq.
  change (((Int.unsigned (add8_u r) - Int.unsigned (add8_u t)) mod Int.modulus -
    Int.unsigned (bit_int cin)) mod Int.modulus mod word_modulus 3 =
    (Int.unsigned (add8_u r) - Int.unsigned (add8_u t) - Int.unsigned (bit_int cin)) mod word_modulus 3).
  rewrite carrier_mod_word by (first [change (0 < 4294967296); lia|exists 16777216; reflexivity]).
  apply carrier_mod_difference_word; [change (0 < 4294967296); lia|exists 16777216; reflexivity].
Qed.
Lemma full_subtract8_values_denote_spec (c : Ty.tySem Bit) left right :
  ((if full_subtract8_borrow (Bit.toBool c) (read8_result left) (read8_result right) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned
      (full_subtract8_payload (Bit.toBool c) (read8_result left) (read8_result right))))) =
    @full_subtract_word_spec Alg.CoreFunSem 3 (c, (decode_word8 left, decode_word8 right)).
Proof.
  assert (HC : Int.unsigned (bit_int (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  rewrite full_subtract8_borrow_numeric, !read8_result_unsigned, HC.
  apply full_subtract_representation_matches.
  rewrite full_subtract8_payload_numeric, !read8_result_unsigned, HC. reflexivity.
Qed.
Lemma wide_full_subtract_borrow_numeric cin r t :
  wide_full_subtract_borrow cin r t =
    (Int64.unsigned r - Int64.unsigned t - Int64.unsigned (bit_long cin) <? 0).
Proof.
  pose proof (Int64.unsigned_range r) as HR. pose proof (Int64.unsigned_range t) as HT.
  pose proof (Int64.unsigned_range (bit_long cin)) as HC.
  unfold wide_full_subtract_borrow.
  change (orb (wide_subtract_borrow r t) (wide_subtract_borrow (Int64.sub r t) (bit_long cin)) =
    (Int64.unsigned r - Int64.unsigned t - Int64.unsigned (bit_long cin) <? 0)).
  rewrite !wide_subtract_borrow_numeric.
  destruct (Int64.unsigned r <? Int64.unsigned t) eqn:HF.
  - apply Z.ltb_lt in HF. cbn [orb]. symmetry. apply Z.ltb_lt. lia.
  - apply Z.ltb_ge in HF. cbn [orb]. unfold Int64.sub.
    rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
    apply borrow_less_difference.
Qed.
Lemma wide_full_subtract_payload_numeric s cin r t :
  @toZ (WordToZ (wide_log s))
    (decode_wide s (Int64.zero_ext (wide_bits s) (wide_full_subtract_payload cin r t))) =
    (Int64.unsigned r - Int64.unsigned t - Int64.unsigned (bit_long cin)) mod word_modulus (wide_log s).
Proof.
  change (@toZ (WordToZ (wide_log s))
    (decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload (Int64.sub r t) (bit_long cin)))) =
    (Int64.unsigned r - Int64.unsigned t - Int64.unsigned (bit_long cin)) mod word_modulus (wide_log s)).
  rewrite wide_subtract_payload_numeric. unfold Int64.sub. rewrite Int64.unsigned_repr_eq.
  apply carrier_mod_difference_word; [change (0 < 18446744073709551616); lia|].
  destruct s; [exists 281474976710656|exists 4294967296|exists 1]; reflexivity.
Qed.
Lemma wide_full_subtract_values_denote_input s (c : Ty.tySem Bit)
    (x y : Ty.tySem (Word (wide_log s))) r t :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  Int64.unsigned t = @toZ (WordToZ (wide_log s)) y ->
  ((if wide_full_subtract_borrow (Bit.toBool c) r t then inr tt else inl tt),
    decode_wide s (Int64.zero_ext (wide_bits s) (wide_full_subtract_payload (Bit.toBool c) r t))) =
    @full_subtract_word_spec Alg.CoreFunSem (wide_log s) (c, (x, y)).
Proof.
  intros HR HT.
  assert (HC : Int64.unsigned (bit_long (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  rewrite wide_full_subtract_borrow_numeric, HR, HT, HC.
  apply full_subtract_representation_matches.
  rewrite wide_full_subtract_payload_numeric, HR, HT, HC. reflexivity.
Qed.

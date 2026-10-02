(** Borrow-input decrement values against the canonical Simplicity composition.
    Shared representation lemmas do not themselves count as C jet coverage. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_add8 C.jet_add8_word C.jet_readBit_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_toZ C.jet_predicate_spec.
Require Import C.jet_subtract_spec C.jet_subtract_word C.jet_full_increment8_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_decrement8_borrow cin r := Int.ltu (Int.zero_ext 8 r) (bit_int cin).
Definition full_decrement8_payload cin r :=
  Int.zero_ext 8 (Int.sub (Int.mul Int.one (Int.zero_ext 8 r)) (bit_int cin)).
Definition wide_full_decrement_borrow cin r := Int64.ltu r (bit_long cin).
Definition wide_full_decrement_payload cin r := Int64.sub r (bit_long cin).

Lemma full_decrement_word_spec_numeric n (c : Ty.tySem Bit) (x : Ty.tySem (Word n)) :
  borrow_word_balance n (@full_decrement_word_spec Alg.CoreFunSem n (c, x)) =
    @toZ (WordToZ n) x - @toZ BitToZ c.
Proof.
  change (borrow_word_balance n (@full_subtract_word_spec Alg.CoreFunSem n
    (c, (x, @Word.zero n Alg.CoreFunSem tt))) = @toZ (WordToZ n) x - @toZ BitToZ c).
  rewrite full_subtract_word_spec_numeric, Word.zero_correct. lia.
Qed.
Lemma full_decrement_representation_matches n (c : Ty.tySem Bit) (x payload : Ty.tySem (Word n)) :
  @toZ (WordToZ n) payload = (@toZ (WordToZ n) x - @toZ BitToZ c) mod word_modulus n ->
  ((if @toZ (WordToZ n) x <? @toZ BitToZ c then inr tt else inl tt), payload) =
    @full_decrement_word_spec Alg.CoreFunSem n (c, x).
Proof.
  intros HP. apply borrow_word_balance_injective. rewrite full_decrement_word_spec_numeric.
  pose proof (word_value_bounds n x) as HX. pose proof (word_modulus_positive n) as HM.
  assert (HC : 0 <= @toZ BitToZ c <= 1) by (destruct c as [[]|[]]; cbn; lia).
  pose proof (borrow_mod_balance (word_modulus n) (@toZ (WordToZ n) x - @toZ BitToZ c)
    HM ltac:(lia)) as HB.
  unfold borrow_word_balance. cbn [fst snd]. rewrite HP, borrow_less_difference.
  destruct (@toZ (WordToZ n) x - @toZ BitToZ c <? 0); exact HB.
Qed.
Lemma full_decrement8_borrow_numeric cin r :
  full_decrement8_borrow cin r = (Int.unsigned (add8_u r) <? Int.unsigned (bit_int cin)).
Proof.
  unfold full_decrement8_borrow, add8_u, Int.ltu.
  destruct (zlt (Int.unsigned (Int.zero_ext 8 r)) (Int.unsigned (bit_int cin)));
    symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma full_decrement8_payload_numeric cin r :
  @toZ (WordToZ 3) (decode_word8 (Int64.repr (Int.unsigned (full_decrement8_payload cin r)))) =
    (Int.unsigned (add8_u r) - Int.unsigned (bit_int cin)) mod word_modulus 3.
Proof.
  assert (Hpayload : full_decrement8_payload cin r = subtract8_payload r (bit_int cin)).
  { unfold full_decrement8_payload, subtract8_payload, add8_u.
    rewrite bit_int_zero_ext8. reflexivity. }
  rewrite Hpayload, subtract8_payload_numeric. unfold add8_u at 2.
  rewrite bit_int_zero_ext8. reflexivity.
Qed.
Lemma full_decrement8_values_denote_spec (c : Ty.tySem Bit) payload :
  ((if full_decrement8_borrow (Bit.toBool c) (read8_result payload) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned (full_decrement8_payload (Bit.toBool c) (read8_result payload))))) =
    @full_decrement_word_spec Alg.CoreFunSem 3 (c, decode_word8 payload).
Proof.
  assert (HC : Int.unsigned (bit_int (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  rewrite full_decrement8_borrow_numeric, read8_result_unsigned, HC.
  apply full_decrement_representation_matches.
  rewrite full_decrement8_payload_numeric, read8_result_unsigned, HC. reflexivity.
Qed.
Lemma wide_full_decrement_borrow_numeric cin r :
  wide_full_decrement_borrow cin r = (Int64.unsigned r <? Int64.unsigned (bit_long cin)).
Proof. apply wide_subtract_borrow_numeric. Qed.
Lemma wide_full_decrement_values_denote_input s (c : Ty.tySem Bit)
    (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  ((if wide_full_decrement_borrow (Bit.toBool c) r then inr tt else inl tt),
    decode_wide s (Int64.zero_ext (wide_bits s) (wide_full_decrement_payload (Bit.toBool c) r))) =
    @full_decrement_word_spec Alg.CoreFunSem (wide_log s) (c, x).
Proof.
  intros HR.
  assert (HC : Int64.unsigned (bit_long (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  rewrite wide_full_decrement_borrow_numeric, HR, HC.
  apply full_decrement_representation_matches.
  change (@toZ (WordToZ (wide_log s))
    (decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload r (bit_long (Bit.toBool c))))) =
    (@toZ (WordToZ (wide_log s)) x - @toZ BitToZ c) mod word_modulus (wide_log s)).
  rewrite wide_subtract_payload_numeric, HR, HC. reflexivity.
Qed.

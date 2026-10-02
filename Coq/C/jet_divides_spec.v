(** Canonical divides is swapped modulo followed by is_zero, including zero
    divisors. These bridges support C calls and are not jet coverage alone. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_division_core_spec C.jet_division_result_spec C.jet_division_value.
Require Import C.jet_test_value_spec C.jet_add8_word C.jet_add8 C.jet_read8 C.jet_spec.
Require Import C.jet_predicate8_exec C.jet_predicate_wide_exec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divides_numeric a b := Z.eqb (division_numeric Datatypes.true b a) 0.
Definition divides8_bit r t := Int.eq Int.zero (division8_raw Datatypes.true t r).
Definition wide_divides_bit r t := Int64.eq Int64.zero (division_wide_raw Datatypes.true t r).

Lemma divides_word_spec_numeric n (x y : Ty.tySem (Word n)) :
  Bit.toBool (@divides_word_spec n Alg.CoreFunSem (x,y)) =
    divides_numeric (@toZ (WordToZ n) x) (@toZ (WordToZ n) y).
Proof.
  change (Bit.toBool (@is_zero_word_spec n Alg.CoreFunSem
    (@modulo_word_spec n Alg.CoreFunSem (y,x))) = divides_numeric (@toZ (WordToZ n) x) (@toZ (WordToZ n) y)).
  rewrite is_zero_word_spec_numeric.
  change (Z.eqb (@toZ (WordToZ n) (@division_word_spec n Datatypes.true Alg.CoreFunSem (y,x))) 0 =
    divides_numeric (@toZ (WordToZ n) x) (@toZ (WordToZ n) y)).
  rewrite division_word_spec_numeric. reflexivity.
Qed.

Lemma divides8_bit_numeric r t :
  divides8_bit r t = divides_numeric (Int.unsigned (add8_u r)) (Int.unsigned (add8_u t)).
Proof.
  unfold divides8_bit, divides_numeric. rewrite Int.eq_sym, int_eq_numeric, Int.unsigned_zero.
  rewrite division8_raw_unsigned. reflexivity.
Qed.

Lemma divides8_denotes w z :
  divides8_bit (read8_result w) (read8_result z) =
    Bit.toBool (@divides_word_spec 3 Alg.CoreFunSem (decode_word8 w,decode_word8 z)).
Proof. rewrite divides8_bit_numeric, !read8_result_unsigned, divides_word_spec_numeric. reflexivity. Qed.

Lemma wide_divides_bit_numeric r t :
  wide_divides_bit r t = divides_numeric (Int64.unsigned r) (Int64.unsigned t).
Proof.
  unfold wide_divides_bit, divides_numeric. rewrite Int64.eq_sym, int64_eq_numeric, Int64.unsigned_zero.
  rewrite division_wide_raw_unsigned. reflexivity.
Qed.

Lemma divides_int64_denotes n (x y : Ty.tySem (Word n)) r t :
  Int64.unsigned r = @toZ (WordToZ n) x -> Int64.unsigned t = @toZ (WordToZ n) y ->
  wide_divides_bit r t = Bit.toBool (@divides_word_spec n Alg.CoreFunSem (x,y)).
Proof. intros HR HT. rewrite wide_divides_bit_numeric, divides_word_spec_numeric, HR, HT. reflexivity. Qed.

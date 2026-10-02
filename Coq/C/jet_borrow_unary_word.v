(** Shared canonical negate/decrement bridges; not additional C-call coverage. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_add8 C.jet_add8_word C.jet_readBit_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec C.jet_subtract_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive unary_borrow_op := UNegate | UDecrement.
Definition unary_borrow_spec k n {term : Alg.Core.Algebra} :=
  match k with UNegate => @negate_word_spec term n | UDecrement => @decrement_word_spec term n end.
Definition unary_borrow_delta k a := match k with UNegate => -a | UDecrement => a - 1 end.
Lemma unary_borrow_spec_parametric k n : Alg.Core.Parametric (fun term => @unary_borrow_spec k n term).
Proof. destruct k; [apply negate_word_spec_parametric|apply decrement_word_spec_parametric]. Qed.

Lemma unary_borrow_spec_numeric k n (x : Ty.tySem (Word n)) :
  borrow_word_balance n (@unary_borrow_spec k n Alg.CoreFunSem x) = unary_borrow_delta k (@toZ (WordToZ n) x).
Proof.
  destruct k.
  - change (borrow_word_balance n (@subtract_word_spec Alg.CoreFunSem n (@Word.zero n Alg.CoreFunSem tt, x)) =
      - @toZ (WordToZ n) x). rewrite subtract_word_spec_numeric, Word.zero_correct. lia.
  - change (borrow_word_balance n (@full_subtract_word_spec Alg.CoreFunSem n (inr tt, (x, @Word.zero n Alg.CoreFunSem tt))) =
      @toZ (WordToZ n) x - 1). rewrite full_subtract_word_spec_numeric, Word.zero_correct.
    change (@toZ (WordToZ n) x - 0 - 1 = @toZ (WordToZ n) x - 1). lia.
Qed.
Lemma unary_borrow_representation_matches k n (x payload : Ty.tySem (Word n)) :
  @toZ (WordToZ n) payload = unary_borrow_delta k (@toZ (WordToZ n) x) mod word_modulus n ->
  ((if unary_borrow_delta k (@toZ (WordToZ n) x) <? 0 then inr tt else inl tt), payload) =
    @unary_borrow_spec k n Alg.CoreFunSem x.
Proof.
  intros HP. apply borrow_word_balance_injective. rewrite unary_borrow_spec_numeric.
  pose proof (word_value_bounds n x) as HX. pose proof (word_modulus_positive n) as HM.
  assert (HD : -word_modulus n <= unary_borrow_delta k (@toZ (WordToZ n) x) < word_modulus n)
    by (destruct k; unfold unary_borrow_delta; lia).
  pose proof (borrow_mod_balance _ _ HM HD) as HB.
  unfold borrow_word_balance. cbn [fst snd]. rewrite HP.
  destruct (unary_borrow_delta k (@toZ (WordToZ n) x) <? 0); exact HB.
Qed.

Definition wide_unary_borrow k r := match k with
  UNegate => negb (Int64.eq r Int64.zero) | UDecrement => Int64.ltu r Int64.one end.
Definition wide_unary_payload k r := match k with
  UNegate => Int64.neg r | UDecrement => Int64.sub r Int64.one end.
Definition unary8_borrow k r := match k with
  UNegate => negb (Int.eq (add8_u r) Int.zero) | UDecrement => Int.lt (add8_u r) Int.one end.
Definition unary8_payload k r := Int.zero_ext 8 (match k with
  UNegate => Int.neg (Int.mul Int.one (add8_u r))
  | UDecrement => Int.sub (Int.mul Int.one (add8_u r)) Int.one end).

Lemma wide_unary_borrow_numeric k r :
  wide_unary_borrow k r = (unary_borrow_delta k (Int64.unsigned r) <? 0).
Proof.
  destruct k.
  - unfold wide_unary_borrow, unary_borrow_delta, Int64.eq. rewrite Int64.unsigned_zero.
    pose proof (Int64.unsigned_range r).
    destruct (zeq (Int64.unsigned r) 0); cbn [negb]; symmetry;
      [apply Z.ltb_ge|apply Z.ltb_lt]; lia.
  - change (wide_subtract_borrow r Int64.one = (Int64.unsigned r - 1 <? 0)).
    rewrite wide_subtract_borrow_numeric, Int64.unsigned_one. apply borrow_less_difference.
Qed.
Lemma wide_unary_payload_numeric k s r :
  @toZ (WordToZ (wide_log s)) (decode_wide s (Int64.zero_ext (wide_bits s) (wide_unary_payload k r))) =
    unary_borrow_delta k (Int64.unsigned r) mod word_modulus (wide_log s).
Proof.
  destruct k.
  - unfold wide_unary_payload. rewrite <- Int64.sub_zero_r.
    change (@toZ (WordToZ (wide_log s))
      (decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload Int64.zero r))) =
      (-Int64.unsigned r) mod word_modulus (wide_log s)).
    rewrite wide_subtract_payload_numeric, Int64.unsigned_zero. reflexivity.
  - change (@toZ (WordToZ (wide_log s))
      (decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload r Int64.one))) =
      (Int64.unsigned r - 1) mod word_modulus (wide_log s)).
    rewrite wide_subtract_payload_numeric, Int64.unsigned_one. reflexivity.
Qed.
Lemma wide_unary_values_denote_input k s (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  ((if wide_unary_borrow k r then inr tt else inl tt),
    decode_wide s (Int64.zero_ext (wide_bits s) (wide_unary_payload k r))) =
    @unary_borrow_spec k (wide_log s) Alg.CoreFunSem x.
Proof.
  intros HR. rewrite wide_unary_borrow_numeric, HR.
  apply unary_borrow_representation_matches. rewrite wide_unary_payload_numeric, HR. reflexivity.
Qed.
Lemma unary8_borrow_numeric k r :
  unary8_borrow k r = (unary_borrow_delta k (Int.unsigned (add8_u r)) <? 0).
Proof.
  destruct k.
  - unfold unary8_borrow, unary_borrow_delta, Int.eq. rewrite Int.unsigned_zero.
    pose proof (Int.unsigned_range (add8_u r)).
    destruct (zeq (Int.unsigned (add8_u r)) 0); cbn [negb]; symmetry;
      [apply Z.ltb_ge|apply Z.ltb_lt]; lia.
  - change (subtract8_borrow r Int.one = (Int.unsigned (add8_u r) - 1 <? 0)).
    rewrite subtract8_borrow_numeric. change
      ((Int.unsigned (add8_u r) <? 1) = (Int.unsigned (add8_u r) - 1 <? 0)).
    apply borrow_less_difference.
Qed.
Lemma unary8_payload_subtract k r : unary8_payload k r =
  match k with UNegate => subtract8_payload Int.zero r | UDecrement => subtract8_payload r Int.one end.
Proof.
  destruct k; unfold unary8_payload, subtract8_payload; rewrite Int.mul_commut, Int.mul_one.
  - change (Int.zero_ext 8 (Int.neg (add8_u r)) = Int.zero_ext 8 (Int.sub Int.zero (add8_u r))).
    f_equal.
  - reflexivity.
Qed.
Lemma unary8_payload_numeric k r :
  @toZ (WordToZ 3) (decode_word8 (Int64.repr (Int.unsigned (unary8_payload k r)))) =
    unary_borrow_delta k (Int.unsigned (add8_u r)) mod word_modulus 3.
Proof.
  rewrite unary8_payload_subtract. destruct k; rewrite subtract8_payload_numeric; reflexivity.
Qed.
Lemma unary8_values_denote_spec k payload :
  ((if unary8_borrow k (read8_result payload) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned (unary8_payload k (read8_result payload))))) =
    @unary_borrow_spec k 3 Alg.CoreFunSem (decode_word8 payload).
Proof.
  rewrite unary8_borrow_numeric, read8_result_unsigned.
  apply unary_borrow_representation_matches. rewrite unary8_payload_numeric, read8_result_unsigned. reflexivity.
Qed.

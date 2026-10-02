(** Canonical Programs.Arith subtraction compositions and representation bridges.
    These helpers are not counted as C jet equivalence proofs. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_complement_spec C.jet_predicate_spec C.jet_toZ.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_subtract_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Ty.Prod Bit (Ty.Prod (Word n) (Word n))) (Ty.Prod Bit (Word n)) :=
  AC.comp
    (AC.pair (Bit.not (AC.take AC.iden))
      (AC.drop (AC.pair (AC.take AC.iden) (AC.comp (AC.drop AC.iden) (@complement_spec n term)))))
    (AC.comp (@Word.fullAdder n term) (AC.pair (Bit.not (AC.take AC.iden)) (AC.drop AC.iden))).
Definition subtract_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) (Ty.Prod Bit (Word n)) :=
  AC.comp (AC.pair Bit.false AC.iden) (@full_subtract_word_spec term n).
Definition negate_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Word n) (Ty.Prod Bit (Word n)) :=
  AC.comp (AC.pair (AC.comp AC.unit (@Word.zero n term)) AC.iden) (@subtract_word_spec term n).
Definition full_decrement_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Ty.Prod Bit (Word n)) (Ty.Prod Bit (Word n)) :=
  AC.comp (AC.pair (AC.take AC.iden)
    (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (@Word.zero n term)))) (@full_subtract_word_spec term n).
Definition decrement_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Word n) (Ty.Prod Bit (Word n)) :=
  AC.comp (AC.pair Bit.true AC.iden) (@full_decrement_word_spec term n).

Lemma full_subtract_word_spec_parametric n : Alg.Core.Parametric (fun term => @full_subtract_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold full_subtract_word_spec.
  repeat first [apply Bit.not_Parametric|apply Word.fullAdder_Parametric|apply complement_spec_parametric|
    apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.take_Parametric|
    apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.
Lemma subtract_word_spec_parametric n : Alg.Core.Parametric (fun term => @subtract_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold subtract_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Bit.false_Parametric|apply Alg.iden_Parametric].
  - apply full_subtract_word_spec_parametric.
Qed.
Lemma negate_word_spec_parametric n : Alg.Core.Parametric (fun term => @negate_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold negate_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Word.zero_Parametric].
    + apply Alg.iden_Parametric.
  - apply subtract_word_spec_parametric.
Qed.
Lemma full_decrement_word_spec_parametric n : Alg.Core.Parametric (fun term => @full_decrement_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold full_decrement_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.take_Parametric. apply Alg.iden_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.drop_Parametric. apply Alg.iden_Parametric.
      * apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Word.zero_Parametric].
  - apply full_subtract_word_spec_parametric.
Qed.
Lemma decrement_word_spec_parametric n : Alg.Core.Parametric (fun term => @decrement_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold decrement_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Bit.true_Parametric|apply Alg.iden_Parametric].
  - apply full_decrement_word_spec_parametric.
Qed.

Lemma complement_spec_numeric n (x : Ty.tySem (Word n)) :
  @toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem x) = word_modulus n - 1 - @toZ (WordToZ n) x.
Proof.
  revert x. induction n as [|n IH]; intros x.
  - destruct x as [[]|[]]; reflexivity.
  - destruct x as [hi lo].
    change (@toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem hi) * word_modulus n +
      @toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem lo) = word_modulus (S n) - 1 -
      (@toZ (WordToZ n) hi * word_modulus n + @toZ (WordToZ n) lo)).
    rewrite !IH, word_modulus_S. ring.
Qed.
Definition bit_complement (c : Ty.tySem Bit) := @complement_spec 0 Alg.CoreFunSem c.
Lemma bit_complement_numeric c : @toZ BitToZ (bit_complement c) = 1 - @toZ BitToZ c.
Proof. exact (complement_spec_numeric 0 c). Qed.
Definition borrow_word_balance n (z : Ty.tySem (Ty.Prod Bit (Word n))) :=
  @toZ (WordToZ n) (snd z) - word_modulus n * @toZ BitToZ (fst z).

Lemma borrow_word_balance_injective n (a b : Ty.tySem (Ty.Prod Bit (Word n))) :
  borrow_word_balance n a = borrow_word_balance n b -> a = b.
Proof.
  destruct a as [c x], b as [d y]. intros H.
  pose proof (word_value_bounds n x) as HX. pose proof (word_value_bounds n y) as HY.
  destruct c as [[]|[]]; destruct d as [[]|[]].
  - change (@toZ (WordToZ n) x - word_modulus n * 0 = @toZ (WordToZ n) y - word_modulus n * 0) in H.
    f_equal. apply (toZ_injective (WordToZ n)). lia.
  - change (@toZ (WordToZ n) x - word_modulus n * 0 = @toZ (WordToZ n) y - word_modulus n * 1) in H.
    exfalso. lia.
  - change (@toZ (WordToZ n) x - word_modulus n * 1 = @toZ (WordToZ n) y - word_modulus n * 0) in H.
    exfalso. lia.
  - change (@toZ (WordToZ n) x - word_modulus n * 1 = @toZ (WordToZ n) y - word_modulus n * 1) in H.
    f_equal. apply (toZ_injective (WordToZ n)). lia.
Qed.

Lemma full_subtract_word_spec_numeric n (c : Ty.tySem Bit) (x y : Ty.tySem (Word n)) :
  borrow_word_balance n (@full_subtract_word_spec Alg.CoreFunSem n (c, (x, y))) =
    @toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c.
Proof.
  pose proof (Word.fullAdder_correct n x (@complement_spec n Alg.CoreFunSem y) (bit_complement c)) as Hsum.
  change (@toZ (PairToZ BitToZ (WordToZ n))
    (@Word.fullAdder n Alg.CoreFunSem (bit_complement c, (x, @complement_spec n Alg.CoreFunSem y))) =
    @toZ (WordToZ n) x + @toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem y) +
    @toZ BitToZ (bit_complement c)) in Hsum.
  change (borrow_word_balance n
    (let z := @Word.fullAdder n Alg.CoreFunSem (bit_complement c, (x, @complement_spec n Alg.CoreFunSem y))
      in (bit_complement (fst z), snd z)) = @toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c).
  destruct (@Word.fullAdder n Alg.CoreFunSem
    (bit_complement c, (x, @complement_spec n Alg.CoreFunSem y))) as [carry payload] eqn:Hout.
  rewrite (@toZ_Pair BitToZ (WordToZ n)), complement_spec_numeric, bit_complement_numeric in Hsum.
  fold (word_modulus n) in Hsum.
  change (@toZ (WordToZ n) payload - word_modulus n * @toZ BitToZ (bit_complement carry) =
    @toZ (WordToZ n) x - @toZ (WordToZ n) y - @toZ BitToZ c).
  rewrite bit_complement_numeric. nia.
Qed.
Lemma subtract_word_spec_numeric n (x y : Ty.tySem (Word n)) :
  borrow_word_balance n (@subtract_word_spec Alg.CoreFunSem n (x, y)) =
    @toZ (WordToZ n) x - @toZ (WordToZ n) y.
Proof.
  change (borrow_word_balance n (@full_subtract_word_spec Alg.CoreFunSem n (inl tt, (x, y))) =
    @toZ (WordToZ n) x - @toZ (WordToZ n) y).
  rewrite full_subtract_word_spec_numeric.
  change (@toZ (WordToZ n) x - @toZ (WordToZ n) y - 0 = @toZ (WordToZ n) x - @toZ (WordToZ n) y). lia.
Qed.
Lemma borrow_mod_balance modulus delta : 0 < modulus -> -modulus <= delta < modulus ->
  delta mod modulus - modulus * (if delta <? 0 then 1 else 0) = delta.
Proof.
  intros HM HD. destruct (delta <? 0) eqn:HC.
  - apply Z.ltb_lt in HC. replace (delta mod modulus) with (delta + modulus); [lia|].
    apply Z.mod_unique with (q := -1); lia.
  - apply Z.ltb_ge in HC. rewrite Z.mod_small by lia. lia.
Qed.
Lemma borrow_less_difference a b : (a <? b) = (a - b <? 0).
Proof.
  destruct (a <? b) eqn:H;
    [apply Z.ltb_lt in H; symmetry; apply Z.ltb_lt|apply Z.ltb_ge in H; symmetry; apply Z.ltb_ge]; lia.
Qed.
Lemma subtract_representation_matches n (x y payload : Ty.tySem (Word n)) :
  @toZ (WordToZ n) payload = (@toZ (WordToZ n) x - @toZ (WordToZ n) y) mod word_modulus n ->
  ((if @toZ (WordToZ n) x <? @toZ (WordToZ n) y then inr tt else inl tt), payload) =
    @subtract_word_spec Alg.CoreFunSem n (x, y).
Proof.
  intros HP. apply borrow_word_balance_injective. rewrite subtract_word_spec_numeric.
  pose proof (word_value_bounds n x) as HX. pose proof (word_value_bounds n y) as HY.
  pose proof (borrow_mod_balance (word_modulus n) (@toZ (WordToZ n) x - @toZ (WordToZ n) y)
    (word_modulus_positive n) ltac:(lia)) as HB.
  unfold borrow_word_balance. cbn [fst snd]. rewrite HP, borrow_less_difference.
  destruct (@toZ (WordToZ n) x - @toZ (WordToZ n) y <? 0); exact HB.
Qed.

(** Exact canonical Programs.Arith.lt/le compositions. These bridges support
    complete C-call proofs; numeric identities alone are not jet coverage. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive order_op := OLt | OLe.
Definition lt_word_spec {term : Alg.Core.Algebra} n :
    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) Bit :=
  AC.comp (@subtract_word_spec term n) (AC.take AC.iden).
Definition le_word_spec {term : Alg.Core.Algebra} n :
    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) Bit :=
  Bit.not (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden)) (@lt_word_spec term n)).
Definition order_word_spec k n {term : Alg.Core.Algebra} :=
  match k with OLt => @lt_word_spec term n | OLe => @le_word_spec term n end.
Definition order_numeric k a b := match k with OLt => a <? b | OLe => a <=? b end.

Lemma lt_word_spec_parametric n : Alg.Core.Parametric (fun term => @lt_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold lt_word_spec. apply Alg.comp_Parametric.
  - apply subtract_word_spec_parametric.
  - apply Alg.take_Parametric. apply Alg.iden_Parametric.
Qed.
Lemma le_word_spec_parametric n : Alg.Core.Parametric (fun term => @le_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold le_word_spec. apply Bit.not_Parametric.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.drop_Parametric. apply Alg.iden_Parametric.
    + apply Alg.take_Parametric. apply Alg.iden_Parametric.
  - apply lt_word_spec_parametric.
Qed.
Lemma order_word_spec_parametric k n : Alg.Core.Parametric (fun term => @order_word_spec k n term).
Proof. destruct k; [apply lt_word_spec_parametric|apply le_word_spec_parametric]. Qed.
Lemma borrow_word_balance_sign n (z : Ty.tySem (Ty.Prod Bit (Word n))) :
  Bit.toBool (fst z) = (borrow_word_balance n z <? 0).
Proof.
  destruct z as [c x]. pose proof (word_value_bounds n x) as HX.
  destruct c as [[]|[]].
  - change (Datatypes.false = (@toZ (WordToZ n) x - word_modulus n * 0 <? 0)).
    symmetry. apply Z.ltb_ge. lia.
  - change (Datatypes.true = (@toZ (WordToZ n) x - word_modulus n * 1 <? 0)).
    symmetry. apply Z.ltb_lt. lia.
Qed.
Lemma lt_word_spec_numeric n (x y : Ty.tySem (Word n)) :
  Bit.toBool (@lt_word_spec Alg.CoreFunSem n (x, y)) =
    (@toZ (WordToZ n) x <? @toZ (WordToZ n) y).
Proof.
  change (Bit.toBool (fst (@subtract_word_spec Alg.CoreFunSem n (x, y))) =
    (@toZ (WordToZ n) x <? @toZ (WordToZ n) y)).
  rewrite borrow_word_balance_sign, subtract_word_spec_numeric. symmetry. apply borrow_less_difference.
Qed.
Lemma le_word_spec_numeric n (x y : Ty.tySem (Word n)) :
  Bit.toBool (@le_word_spec Alg.CoreFunSem n (x, y)) =
    (@toZ (WordToZ n) x <=? @toZ (WordToZ n) y).
Proof.
  change (Bit.toBool (@Bit.not (Ty.Prod (Word n) (Word n)) Alg.CoreFunSem
    (@lt_word_spec Alg.CoreFunSem n) (y, x)) =
    (@toZ (WordToZ n) x <=? @toZ (WordToZ n) y)).
  assert (Hnot : Bit.toBool (@Bit.not (Ty.Prod (Word n) (Word n)) Alg.CoreFunSem
    (@lt_word_spec Alg.CoreFunSem n) (y, x)) =
      negb (Bit.toBool (@lt_word_spec Alg.CoreFunSem n (y, x)))).
  { change (Bit.toBool (match @lt_word_spec Alg.CoreFunSem n (y, x) with
      | inl _ => inr tt | inr _ => inl tt end) =
      negb (Bit.toBool (@lt_word_spec Alg.CoreFunSem n (y, x)))).
    destruct (@lt_word_spec Alg.CoreFunSem n (y, x)) as [[]|[]]; reflexivity. }
  rewrite Hnot, lt_word_spec_numeric.
  destruct (@toZ (WordToZ n) y <? @toZ (WordToZ n) x) eqn:H;
    [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; cbn [negb]; symmetry;
    [apply Z.leb_gt|apply Z.leb_le]; lia.
Qed.
Lemma order_word_spec_numeric k n (x y : Ty.tySem (Word n)) :
  Bit.toBool (@order_word_spec k n Alg.CoreFunSem (x, y)) =
    order_numeric k (@toZ (WordToZ n) x) (@toZ (WordToZ n) y).
Proof. destruct k; [apply lt_word_spec_numeric|apply le_word_spec_numeric]. Qed.

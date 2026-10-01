(** Exact Programs.Generic.eq recursion, shared by the equality jet widths.
    The logical/numeric bridges support actual C call proofs; they do not
    themselves count as implementation equivalence. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ.
Set Default Timeout 10.
Local Notation "s &&* t" := (Alg.Core.Combinators.pair s t) (at level 70, right associativity).
Local Notation "s >>* t" := (Alg.Core.Combinators.comp s t) (at level 90, right associativity).
Local Notation "'H'" := Alg.Core.Combinators.iden.
Local Notation "'O' x" := (Alg.Core.Combinators.take x) (at level 0, right associativity).
Local Notation "'I' x" := (Alg.Core.Combinators.drop x) (at level 0, right associativity).

Fixpoint equality_spec A {term : Alg.Core.Algebra} : @Alg.Core.domain term (Ty.Prod A A) Bit :=
  match A with
  | Ty.Unit => Bit.true
  | Ty.Sum L R => Alg.Core.Combinators.case
      (Alg.Core.Combinators.swapP >>* Alg.Core.Combinators.case (equality_spec L) Bit.false)
      (Alg.Core.Combinators.swapP >>* Alg.Core.Combinators.case Bit.false (equality_spec R))
  | Ty.Prod L R =>
      ((O O H &&* I O H >>* equality_spec L) &&* (O I H &&* I I H))
        >>* Bit.cond (equality_spec R) Bit.false
  end.

Lemma equality_spec_parametric A : Alg.Core.Parametric (@equality_spec A).
Proof.
  intros alg1 alg2 Rel. induction A; cbn [equality_spec].
  - apply Bit.true_Parametric.
  - apply Alg.case_Parametric; apply Alg.comp_Parametric.
    + apply Alg.swapP_Parametric.
    + apply Alg.case_Parametric; [exact IHA1|apply Bit.false_Parametric].
    + apply Alg.swapP_Parametric.
    + apply Alg.case_Parametric; [apply Bit.false_Parametric|exact IHA2].
  - apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.comp_Parametric; [|exact IHA1].
        apply Alg.pair_Parametric.
        -- apply Alg.take_Parametric. apply Alg.take_Parametric. apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric. apply Alg.take_Parametric. apply Alg.iden_Parametric.
      * apply Alg.pair_Parametric.
        -- apply Alg.take_Parametric. apply Alg.drop_Parametric. apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric. apply Alg.drop_Parametric. apply Alg.iden_Parametric.
    + apply Bit.cond_Parametric; [exact IHA2|apply Bit.false_Parametric].
Qed.

Lemma equality_spec_product L R (xh yh : Ty.tySem L) (xl yl : Ty.tySem R) :
  Bit.toBool (@equality_spec (Ty.Prod L R) Alg.CoreFunSem ((xh, xl), (yh, yl))) =
    andb (Bit.toBool (@equality_spec L Alg.CoreFunSem (xh, yh)))
      (Bit.toBool (@equality_spec R Alg.CoreFunSem (xl, yl))).
Proof.
  cbn [equality_spec]. cbn -[equality_spec].
  destruct (@equality_spec L Alg.CoreFunSem (xh, yh)) as [[]|[]]; reflexivity.
Qed.

Lemma equality_spec_true A (x y : Ty.tySem A) :
  Bit.toBool (@equality_spec A Alg.CoreFunSem (x, y)) = Datatypes.true <-> x = y.
Proof.
  revert x y. induction A; intros x y.
  - destruct x, y; split; reflexivity.
  - destruct x as [x|x], y as [y|y]; cbn [equality_spec]; cbn -[equality_spec].
    + rewrite IHA1. split; intros; congruence.
    + split; discriminate.
    + split; discriminate.
    + rewrite IHA2. split; intros; congruence.
  - destruct x as [xh xl], y as [yh yl].
    rewrite equality_spec_product, Bool.andb_true_iff, IHA1, IHA2.
    split; [intros [-> ->]; reflexivity|intros Hxy; injection Hxy; auto].
Qed.

Lemma equality_spec_word_numeric n (x y : Ty.tySem (Word n)) :
  Bit.toBool (@equality_spec (Word n) Alg.CoreFunSem (x, y)) =
    Z.eqb (@toZ (WordToZ n) x) (@toZ (WordToZ n) y).
Proof.
  apply Bool.eq_true_iff_eq. rewrite equality_spec_true, Z.eqb_eq.
  split; [intros ->; reflexivity|apply toZ_injective].
Qed.

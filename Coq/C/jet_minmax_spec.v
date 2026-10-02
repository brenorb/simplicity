(** Literal canonical Programs.Arith.min/max: le &&& iden, then cond.
    The C's strict comparison chooses the other equal input at equality. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_order_spec C.jet_toZ.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition minmax_word_spec n (maximum : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) (Word n) :=
  AC.comp (AC.pair (@le_word_spec term n) AC.iden)
    (if maximum then Bit.cond (AC.drop AC.iden) (AC.take AC.iden)
     else Bit.cond (AC.take AC.iden) (AC.drop AC.iden)).
Definition minmax_select {A : Type} (maximum less : bool) (x y : A) :=
  if less then (if maximum then y else x) else (if maximum then x else y).

Lemma minmax_word_spec_parametric n maximum : Alg.Core.Parametric (@minmax_word_spec n maximum).
Proof.
  intros alg1 alg2 R. unfold minmax_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply le_word_spec_parametric|apply Alg.iden_Parametric].
  - destruct maximum; apply Bit.cond_Parametric.
    all: first [apply Alg.take_Parametric|apply Alg.drop_Parametric]; apply Alg.iden_Parametric.
Qed.
Lemma minmax_word_spec_le n maximum (x y : Ty.tySem (Word n)) :
  @minmax_word_spec n maximum Alg.CoreFunSem (x, y) =
    minmax_select maximum (Bit.toBool (@le_word_spec Alg.CoreFunSem n (x, y))) x y.
Proof.
  destruct maximum.
  - change ((match @le_word_spec Alg.CoreFunSem n (x, y) with
      | inl _ => x | inr _ => y end) =
      minmax_select Datatypes.true (Bit.toBool (@le_word_spec Alg.CoreFunSem n (x, y))) x y).
    destruct (@le_word_spec Alg.CoreFunSem n (x, y)) as [[]|[]]; reflexivity.
  - change ((match @le_word_spec Alg.CoreFunSem n (x, y) with
      | inl _ => y | inr _ => x end) =
      minmax_select Datatypes.false (Bit.toBool (@le_word_spec Alg.CoreFunSem n (x, y))) x y).
    destruct (@le_word_spec Alg.CoreFunSem n (x, y)) as [[]|[]]; reflexivity.
Qed.
Lemma minmax_word_spec_strict n maximum (x y : Ty.tySem (Word n)) :
  @minmax_word_spec n maximum Alg.CoreFunSem (x, y) =
    minmax_select maximum (@toZ (WordToZ n) x <? @toZ (WordToZ n) y) x y.
Proof.
  rewrite minmax_word_spec_le, le_word_spec_numeric.
  destruct (@toZ (WordToZ n) x <=? @toZ (WordToZ n) y) eqn:Hle,
    (@toZ (WordToZ n) x <? @toZ (WordToZ n) y) eqn:Hlt; try reflexivity.
  - apply Z.leb_le in Hle. apply Z.ltb_ge in Hlt.
    assert (Hxy : x = y) by (apply (toZ_injective (WordToZ n)); lia).
    subst y. destruct maximum; reflexivity.
  - apply Z.leb_gt in Hle. apply Z.ltb_lt in Hlt. exfalso; lia.
Qed.

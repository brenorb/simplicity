(** Literal canonical Programs.Arith.median min/max composition. Its bridge
    follows the nested strict comparisons of the actual C implementation. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_minmax_spec C.jet_toZ.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition median_word_spec n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word n) (Ty.Prod (Word n) (Word n))) (Word n) :=
  AC.comp
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden)))
            (@minmax_word_spec n Datatypes.false term))
          (AC.comp (AC.pair (AC.take AC.iden) (AC.drop (AC.drop AC.iden)))
            (@minmax_word_spec n Datatypes.false term)))
        (@minmax_word_spec n Datatypes.true term))
      (AC.drop (@minmax_word_spec n Datatypes.false term)))
    (@minmax_word_spec n Datatypes.true term).
Definition median_select {A : Type} (less : A -> A -> bool) (x y z : A) :=
  if less x y then
    if less y z then y else if less z x then x else z
  else if less x z then x else if less z y then y else z.

Lemma median_word_spec_parametric n : Alg.Core.Parametric (@median_word_spec n).
Proof.
  intros alg1 alg2 R. unfold median_word_spec.
  repeat first [apply minmax_word_spec_parametric|apply Alg.comp_Parametric|
    apply Alg.pair_Parametric|apply Alg.take_Parametric|apply Alg.drop_Parametric|
    apply Alg.iden_Parametric].
Qed.
Lemma minmax_word_spec_numeric n maximum (x y : Ty.tySem (Word n)) :
  @toZ (WordToZ n) (@minmax_word_spec n maximum Alg.CoreFunSem (x, y)) =
    if maximum then Z.max (@toZ (WordToZ n) x) (@toZ (WordToZ n) y)
    else Z.min (@toZ (WordToZ n) x) (@toZ (WordToZ n) y).
Proof.
  rewrite minmax_word_spec_strict. unfold minmax_select.
  destruct (@toZ (WordToZ n) x <? @toZ (WordToZ n) y) eqn:HL;
    [apply Z.ltb_lt in HL|apply Z.ltb_ge in HL]; destruct maximum; symmetry.
  - apply Z.max_r; lia.
  - apply Z.min_l; lia.
  - apply Z.max_l; lia.
  - apply Z.min_r; lia.
Qed.
Lemma median_minmax_numeric a b c :
  Z.max (Z.max (Z.min a b) (Z.min a c)) (Z.min b c) = median_select Z.ltb a b c.
Proof.
  unfold median_select.
  destruct (a <? b) eqn:Hxy; [apply Z.ltb_lt in Hxy|apply Z.ltb_ge in Hxy].
  - destruct (b <? c) eqn:Hyz; [apply Z.ltb_lt in Hyz|apply Z.ltb_ge in Hyz].
    + repeat first [rewrite Z.min_l by lia|rewrite Z.min_r by lia|
        rewrite Z.max_l by lia|rewrite Z.max_r by lia]; reflexivity.
    + destruct (c <? a) eqn:Hzx; [apply Z.ltb_lt in Hzx|apply Z.ltb_ge in Hzx].
      all: repeat first [rewrite Z.min_l by lia|rewrite Z.min_r by lia|
        rewrite Z.max_l by lia|rewrite Z.max_r by lia]; reflexivity.
  - destruct (a <? c) eqn:Hxz; [apply Z.ltb_lt in Hxz|apply Z.ltb_ge in Hxz].
    + repeat first [rewrite Z.min_l by lia|rewrite Z.min_r by lia|
        rewrite Z.max_l by lia|rewrite Z.max_r by lia]; reflexivity.
    + destruct (c <? b) eqn:Hzy; [apply Z.ltb_lt in Hzy|apply Z.ltb_ge in Hzy].
      all: repeat first [rewrite Z.min_l by lia|rewrite Z.min_r by lia|
        rewrite Z.max_l by lia|rewrite Z.max_r by lia]; reflexivity.
Qed.
Lemma median_word_spec_strict n (x y z : Ty.tySem (Word n)) :
  @median_word_spec n Alg.CoreFunSem (x, (y, z)) =
    median_select (fun a b => @toZ (WordToZ n) a <? @toZ (WordToZ n) b) x y z.
Proof.
  apply (toZ_injective (WordToZ n)).
  change (@toZ (WordToZ n) (@minmax_word_spec n Datatypes.true Alg.CoreFunSem
    (@minmax_word_spec n Datatypes.true Alg.CoreFunSem
      (@minmax_word_spec n Datatypes.false Alg.CoreFunSem (x, y),
       @minmax_word_spec n Datatypes.false Alg.CoreFunSem (x, z)),
     @minmax_word_spec n Datatypes.false Alg.CoreFunSem (y, z))) =
    @toZ (WordToZ n) (median_select
      (fun a b => @toZ (WordToZ n) a <? @toZ (WordToZ n) b) x y z)).
  rewrite !minmax_word_spec_numeric, median_minmax_numeric.
  unfold median_select.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

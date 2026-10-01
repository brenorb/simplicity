(** Exact canonical Programs.Word.some/all recursion and a shared symbolic
    bridge to the integer comparisons used by the C jets. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Arith.
Require Import C.jet_word_repr.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint predicate_spec n (all : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) Bit :=
  match n with
  | O => @Alg.Core.Combinators.iden Bit term
  | S n =>
      let hi := @Alg.Core.Combinators.take (Word n) (Word n) Bit term (predicate_spec n all) in
      let lo := @Alg.Core.Combinators.drop (Word n) (Word n) Bit term (predicate_spec n all) in
      if all then Bit.and hi lo else Bit.or hi lo
  end.

Lemma predicate_spec_parametric n all : Alg.Core.Parametric (@predicate_spec n all).
Proof.
  intros alg1 alg2 R. induction n; cbn [predicate_spec].
  - apply Alg.iden_Parametric.
  - destruct all; [apply Bit.and_Parametric|apply Bit.or_Parametric].
    all: first [apply Alg.take_Parametric|apply Alg.drop_Parametric]; exact IHn.
Qed.

Definition word_modulus n := two_power_nat (ToZ.Theory.bitSize (WordToZ n)).
Definition predicate_numeric n (all : bool) v :=
  if all then Z.eqb v (word_modulus n - 1) else negb (Z.eqb v 0).

Lemma word_modulus_positive n : 0 < word_modulus n.
Proof. unfold word_modulus. rewrite two_power_nat_equiv. apply Z.pow_pos_nonneg; lia. Qed.
Lemma word_modulus_S n : word_modulus (S n) = word_modulus n * word_modulus n.
Proof.
  change (two_power_nat (ToZ.Theory.bitSize (WordToZ n) + ToZ.Theory.bitSize (WordToZ n)) =
    two_power_nat (ToZ.Theory.bitSize (WordToZ n)) * two_power_nat (ToZ.Theory.bitSize (WordToZ n))).
  apply two_power_nat_plus.
Qed.
Lemma word_value_bounds n (x : Ty.tySem (Word n)) :
  0 <= @toZ (WordToZ n) x < word_modulus n.
Proof.
  unfold word_modulus. rewrite two_power_nat_equiv, word_bitSize. apply word_toZ_range.
Qed.

Lemma predicate_numeric_pair n all a b :
  0 <= a < word_modulus n -> 0 <= b < word_modulus n ->
  predicate_numeric (S n) all (a * word_modulus n + b) =
    if all then andb (predicate_numeric n all a) (predicate_numeric n all b)
    else orb (predicate_numeric n all a) (predicate_numeric n all b).
Proof.
  intros Ha Hb. pose proof (word_modulus_positive n) as HB.
  destruct all.
  - change (Z.eqb (a * word_modulus n + b) (word_modulus (S n) - 1) =
      andb (Z.eqb a (word_modulus n - 1)) (Z.eqb b (word_modulus n - 1))).
    rewrite word_modulus_S.
    destruct (Z.eqb_spec a (word_modulus n - 1)), (Z.eqb_spec b (word_modulus n - 1));
      cbn -[word_modulus].
    all: first [apply Z.eqb_eq|apply Z.eqb_neq]; nia.
  - change (negb (Z.eqb (a * word_modulus n + b) 0) = orb (negb (Z.eqb a 0)) (negb (Z.eqb b 0))).
    destruct (Z.eqb_spec a 0), (Z.eqb_spec b 0);
      destruct (Z.eqb_spec (a * word_modulus n + b) 0); cbn -[word_modulus]; try reflexivity; nia.
Qed.

Lemma predicate_spec_numeric n all (x : Ty.tySem (Word n)) :
  Bit.toBool (@predicate_spec n all Alg.CoreFunSem x) =
    predicate_numeric n all (@toZ (WordToZ n) x).
Proof.
  revert x. induction n as [|n IH]; intros x.
  - destruct all, x as [[]|[]]; reflexivity.
  - destruct x as [hi lo].
    change (Bit.toBool (@predicate_spec (S n) all Alg.CoreFunSem (hi, lo)) =
      predicate_numeric (S n) all (@toZ (WordToZ n) hi * word_modulus n + @toZ (WordToZ n) lo)).
    rewrite predicate_numeric_pair by apply word_value_bounds.
    rewrite <- !IH.
    destruct all; cbn [predicate_spec].
    all: cbn -[predicate_spec].
    + destruct (@predicate_spec n Datatypes.true Alg.CoreFunSem hi) as [[]|[]];
        destruct (@predicate_spec n Datatypes.true Alg.CoreFunSem lo) as [[]|[]]; reflexivity.
    + destruct (@predicate_spec n Datatypes.false Alg.CoreFunSem hi) as [[]|[]];
        destruct (@predicate_spec n Datatypes.false Alg.CoreFunSem lo) as [[]|[]]; reflexivity.
Qed.

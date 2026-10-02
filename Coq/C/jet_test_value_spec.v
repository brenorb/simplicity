(** Literal canonical Programs.Arith.is_zero/is_one compositions. Numeric
    bridges support implementation proofs, and do not themselves count as jets. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_predicate_spec C.jet_subtract_spec C.jet_borrow_unary_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition is_zero_word_spec n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) Bit := Bit.not (@predicate_spec n Datatypes.false term).
Definition is_one_word_spec n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) Bit :=
  AC.comp (@decrement_word_spec term n) (AC.drop (@is_zero_word_spec n term)).
Definition test_value_spec n (one : bool) {term : Alg.Core.Algebra} :=
  if one then @is_one_word_spec n term else @is_zero_word_spec n term.
Definition test_value_numeric (one : bool) v := Z.eqb v (if one then 1 else 0).

Lemma is_zero_word_spec_parametric n : Alg.Core.Parametric (@is_zero_word_spec n).
Proof.
  intros alg1 alg2 R. unfold is_zero_word_spec. apply Bit.not_Parametric.
  apply predicate_spec_parametric.
Qed.
Lemma is_one_word_spec_parametric n : Alg.Core.Parametric (@is_one_word_spec n).
Proof.
  intros alg1 alg2 R. unfold is_one_word_spec. apply Alg.comp_Parametric.
  - apply decrement_word_spec_parametric.
  - apply Alg.drop_Parametric. apply is_zero_word_spec_parametric.
Qed.
Lemma test_value_spec_parametric n one : Alg.Core.Parametric (@test_value_spec n one).
Proof. destruct one; [apply is_one_word_spec_parametric|apply is_zero_word_spec_parametric]. Qed.

Lemma is_zero_word_spec_numeric n (x : Ty.tySem (Word n)) :
  Bit.toBool (@is_zero_word_spec n Alg.CoreFunSem x) = Z.eqb (@toZ (WordToZ n) x) 0.
Proof.
  change (Bit.toBool (match @predicate_spec n Datatypes.false Alg.CoreFunSem x with
    | inl _ => inr tt | inr _ => inl tt end) = Z.eqb (@toZ (WordToZ n) x) 0).
  assert (HN : Bit.toBool (match @predicate_spec n Datatypes.false Alg.CoreFunSem x with
    | inl _ => inr tt | inr _ => inl tt end) =
    negb (Bit.toBool (@predicate_spec n Datatypes.false Alg.CoreFunSem x))).
  { destruct (@predicate_spec n Datatypes.false Alg.CoreFunSem x) as [[]|[]]; reflexivity. }
  rewrite HN, predicate_spec_numeric. unfold predicate_numeric. apply Bool.negb_involutive.
Qed.
Lemma word_modulus_at_least_two n : 2 <= word_modulus n.
Proof.
  induction n as [|n IH]; [change (2 <= 2); lia|]. rewrite word_modulus_S. nia.
Qed.
Lemma decrement_payload_zero_iff_one n (x : Ty.tySem (Word n)) :
  Z.eqb (@toZ (WordToZ n) (snd (@decrement_word_spec Alg.CoreFunSem n x))) 0 =
    Z.eqb (@toZ (WordToZ n) x) 1.
Proof.
  pose proof (unary_borrow_spec_numeric UDecrement n x) as Hbalance.
  change (borrow_word_balance n (@decrement_word_spec Alg.CoreFunSem n x) =
    @toZ (WordToZ n) x - 1) in Hbalance.
  destruct (@decrement_word_spec Alg.CoreFunSem n x) as [borrow payload] eqn:HD.
  pose proof (word_value_bounds n x) as HX.
  pose proof (word_value_bounds n payload) as HP.
  pose proof (word_modulus_at_least_two n) as HM.
  unfold borrow_word_balance in Hbalance. cbn [fst snd] in Hbalance |- *.
  destruct borrow as [[]|[]]; change (@toZ BitToZ _) with 0 in Hbalance ||
    change (@toZ BitToZ _) with 1 in Hbalance.
  all: destruct (Z.eqb_spec (@toZ (WordToZ n) payload) 0),
      (Z.eqb_spec (@toZ (WordToZ n) x) 1); try reflexivity; exfalso; lia.
Qed.
Lemma is_one_word_spec_numeric n (x : Ty.tySem (Word n)) :
  Bit.toBool (@is_one_word_spec n Alg.CoreFunSem x) = Z.eqb (@toZ (WordToZ n) x) 1.
Proof.
  change (Bit.toBool (@is_zero_word_spec n Alg.CoreFunSem
    (snd (@decrement_word_spec Alg.CoreFunSem n x))) = Z.eqb (@toZ (WordToZ n) x) 1).
  rewrite is_zero_word_spec_numeric. apply decrement_payload_zero_iff_one.
Qed.
Lemma test_value_spec_numeric n one (x : Ty.tySem (Word n)) :
  Bit.toBool (@test_value_spec n one Alg.CoreFunSem x) = test_value_numeric one (@toZ (WordToZ n) x).
Proof. destruct one; [apply is_one_word_spec_numeric|apply is_zero_word_spec_numeric]. Qed.

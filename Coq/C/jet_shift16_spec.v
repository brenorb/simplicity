(** Exact CoreJets left/right_shift word4 word16 adapters. Control normalization
    computes 16 control values only, leaving the 16-bit payload symbolic. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_shift_spec C.jet_rotate_control_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift16_plain_spec right {term : Alg.Core.Algebra} := @shift_word_spec 2 4 right term.

Lemma shift16_plain_spec_parametric right : Alg.Core.Parametric (@shift16_plain_spec right).
Proof. apply shift_word_spec_parametric. Qed.

Lemma shift16_controls_normalform right amount (x : Ty.tySem (Word 4)) :
  @shift16_plain_spec right Alg.CoreFunSem (amount,x) =
    @Word.shift_const 4 Alg.CoreFunSem (rotate_signed_amount right (@toZ (WordToZ 2) amount)) x.
Proof.
  destruct x as [[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]].
  destruct right; destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]].
  all: cbn; reflexivity.
Qed.

Lemma shift16_plain_spec_bits right amount x j : 0 <= j < 16 ->
  Z.testbit (@toZ (WordToZ 4) (@shift16_plain_spec right Alg.CoreFunSem (amount,x))) j =
    Z.testbit (@toZ (WordToZ 4) x) (j - rotate_signed_amount right (@toZ (WordToZ 2) amount)).
Proof.
  intros Hj. rewrite shift16_controls_normalform.
  pose proof (@Word.shift_const_correct 4
    (-rotate_signed_amount right (@toZ (WordToZ 2) amount)) x j Hj) as H.
  rewrite Z.opp_involutive in H.
  replace (j + -rotate_signed_amount right (@toZ (WordToZ 2) amount))
    with (j - rotate_signed_amount right (@toZ (WordToZ 2) amount)) in H by lia.
  exact H.
Qed.

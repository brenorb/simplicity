(** Exact CoreJets left/right_shift word8 word32 adapters. Control normalization
    computes 256 control values only, leaving the 32-bit payload symbolic. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_shift_spec C.jet_rotate_control_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift32_plain_spec right {term : Alg.Core.Algebra} := @shift_word_spec 3 5 right term.

Lemma shift32_plain_spec_parametric right : Alg.Core.Parametric (@shift32_plain_spec right).
Proof. apply shift_word_spec_parametric. Qed.

Lemma shift32_controls_normalform right amount (x : Ty.tySem (Word 5)) :
  @shift32_plain_spec right Alg.CoreFunSem (amount,x) =
    @Word.shift_const 5 Alg.CoreFunSem (rotate_signed_amount right (@toZ (WordToZ 3) amount)) x.
Proof.
  destruct x as [[[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]] [[[[x16 x17] [x18 x19]] [[x20 x21] [x22 x23]]] [[[x24 x25] [x26 x27]] [[x28 x29] [x30 x31]]]]].
  destruct right; destruct amount as [[[a b] [c d]] [[e f] [g h]]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
      e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  (* Bound each batch under the unchanged default timeout. One aggregate
     command over all 512 control/direction cases exceeds that bound. *)
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
  1-16: cbn; reflexivity.
Qed.

Lemma shift32_plain_spec_bits right amount x j : 0 <= j < 32 ->
  Z.testbit (@toZ (WordToZ 5) (@shift32_plain_spec right Alg.CoreFunSem (amount,x))) j =
    Z.testbit (@toZ (WordToZ 5) x) (j - rotate_signed_amount right (@toZ (WordToZ 3) amount)).
Proof.
  intros Hj. rewrite shift32_controls_normalform.
  pose proof (@Word.shift_const_correct 5
    (-rotate_signed_amount right (@toZ (WordToZ 3) amount)) x j Hj) as H.
  rewrite Z.opp_involutive in H.
  replace (j + -rotate_signed_amount right (@toZ (WordToZ 3) amount))
    with (j - rotate_signed_amount right (@toZ (WordToZ 3) amount)) in H by lia.
  exact H.
Qed.

(** Literal CoreJets left/right_rotate_8 programs. The fourth control bit
    reaches the canonical SingleV identity step; it is not discarded in the
    program definition. Only the control normal form removes that identity. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec C.jet_rotate_spec C.jet_right_rotate_spec.
Require Import C.jet_rotate16_spec C.jet_rotate_control_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate8_spec (right : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word 2) (Word 3)) (Word 3) :=
  if right then @right_rotate_word_spec 2 3 term else @left_rotate_word_spec 2 3 term.

Lemma rotate8_spec_parametric right : Alg.Core.Parametric (@rotate8_spec right).
Proof. destruct right; [apply right_rotate_word_spec_parametric|apply left_rotate_word_spec_parametric]. Qed.

Lemma rotate8_controls_normalform right amount (x : Ty.tySem (Word 3)) :
  @rotate8_spec right Alg.CoreFunSem (amount,x) = rotate_control_word_fun 2 3 right 0 3 amount x.
Proof.
  destruct right; destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]]; reflexivity.
Qed.

Lemma rotate_control_nibble_amount3 amount :
  rotate_control_word_amount 2 0 3 amount = @toZ (WordToZ 2) amount mod 8.
Proof.
  destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]]; reflexivity.
Qed.

Lemma rotate8_spec_bits right amount x j : 0 <= j < 8 ->
  Z.testbit (@toZ (WordToZ 3) (@rotate8_spec right Alg.CoreFunSem (amount,x))) j =
    Z.testbit (@toZ (WordToZ 3) x)
      ((j - rotate_signed_amount right (@toZ (WordToZ 2) amount mod 8)) mod 8).
Proof.
  intros Hj. rewrite rotate8_controls_normalform, rotate_control_word_bits by exact Hj.
  rewrite rotate_control_nibble_amount3. reflexivity.
Qed.

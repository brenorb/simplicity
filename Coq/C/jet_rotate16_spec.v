(** Exact CoreJets left/right_rotate_16 canonical variable-control programs.
    Word4 controls exhaust before SingleV; the literal recursion is retained. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec C.jet_rotate_spec C.jet_right_rotate_spec C.jet_rotate_control_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate16_spec (right : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word 2) (Word 4)) (Word 4) :=
  if right then @right_rotate_word_spec 2 4 term else @left_rotate_word_spec 2 4 term.

Lemma word4_reverse_items_spec {term : Alg.Core.Algebra} :
  rev (@vector_items_spec Bit 2 term) =
    map (fun i => @word_bit_spec 2 i term) (List.seq 0 4).
Proof. reflexivity. Qed.

Lemma rotate16_spec_parametric right : Alg.Core.Parametric (@rotate16_spec right).
Proof. destruct right; [apply right_rotate_word_spec_parametric|apply left_rotate_word_spec_parametric]. Qed.

Lemma rotate16_controls_normalform right amount (x : Ty.tySem (Word 4)) :
  @rotate16_spec right Alg.CoreFunSem (amount,x) = rotate_control_word_fun 2 4 right 0 4 amount x.
Proof.
  destruct right; destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]]; reflexivity.
Qed.

Lemma rotate_control_nibble_amount4 amount :
  rotate_control_word_amount 2 0 4 amount = @toZ (WordToZ 2) amount mod 16.
Proof.
  destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]]; reflexivity.
Qed.

Lemma rotate16_spec_bits right amount x j : 0 <= j < 16 ->
  Z.testbit (@toZ (WordToZ 4) (@rotate16_spec right Alg.CoreFunSem (amount,x))) j =
    Z.testbit (@toZ (WordToZ 4) x)
      ((j - rotate_signed_amount right (@toZ (WordToZ 2) amount mod 16)) mod 16).
Proof.
  intros Hj. rewrite rotate16_controls_normalform, rotate_control_word_bits by exact Hj.
  rewrite rotate_control_nibble_amount4. reflexivity.
Qed.

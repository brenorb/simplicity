(** Literal fill-input canonical byte shifts. The complement normal form is
    a bridge for the C helper's two XOR toggles, not a substituted spec. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_shift_spec C.jet_shift8_spec C.jet_complement_spec C.jet_shift8_fill_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift8_with_spec right {term : Alg.Core.Algebra} := @shift_with_word_spec 2 3 right term.

Lemma shift8_with_spec_parametric right : Alg.Core.Parametric (@shift8_with_spec right).
Proof. apply shift_with_word_spec_parametric. Qed.

Lemma bit_flip_twice (b : Ty.tySem Bit) :
  (match (match b with inl _ => inr tt | inr _ => inl tt end) with
   | inl _ => inr tt | inr _ => inl tt end) = b.
Proof. destruct b as [[]|[]]; reflexivity. Qed.

Lemma shift8_with_complement_normalform right fill amount (x : Ty.tySem (Word 3)) :
  @shift8_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)) =
    if fill then @complement_spec 3 Alg.CoreFunSem
      (@shift8_plain_spec right Alg.CoreFunSem (amount, @complement_spec 3 Alg.CoreFunSem x))
    else @shift8_plain_spec right Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]].
  destruct fill, right; destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]].
  all: cbn; repeat rewrite bit_flip_twice; reflexivity.
Qed.

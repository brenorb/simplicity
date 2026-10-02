(** Literal fill-input canonical 16-bit shifts. The complement normal form is
    a bridge for the C helper's two XOR toggles, not a substituted spec. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_shift_spec C.jet_shift16_spec C.jet_complement_spec C.jet_shift8_with_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift16_with_spec right {term : Alg.Core.Algebra} := @shift_with_word_spec 2 4 right term.

Lemma shift16_with_spec_parametric right : Alg.Core.Parametric (@shift16_with_spec right).
Proof. apply shift_with_word_spec_parametric. Qed.

Lemma shift16_with_complement_normalform right fill amount (x : Ty.tySem (Word 4)) :
  @shift16_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)) =
    if fill then @complement_spec 4 Alg.CoreFunSem
      (@shift16_plain_spec right Alg.CoreFunSem (amount, @complement_spec 4 Alg.CoreFunSem x))
    else @shift16_plain_spec right Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]].
  destruct fill, right; destruct amount as [[a b] [c d]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]].
  all: cbn; repeat rewrite bit_flip_twice; reflexivity.
Qed.

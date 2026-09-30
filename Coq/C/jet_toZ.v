(** Shared injectivity of the canonical integer interpretation. *)
From Coq Require Import ZArith.
Require Import Simplicity.Word Simplicity.Bit.

Lemma toZ_injective (T : ToZ.type) (x y : Ty.tySem T) :
  @toZ T x = @toZ T y -> x = y.
Proof. intros H. rewrite <- (from_toZ x), <- (from_toZ y), H. reflexivity. Qed.

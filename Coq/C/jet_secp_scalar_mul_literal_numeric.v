(** Numeric adapters for the existing literal canonical multiplication term.
    The literal term is retained as the implementation proof's output. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_word_repr C.jet_multiply_spec C.jet_secp_canonical_scalar
  C.jet_secp_canonical_scalar_negate.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma canonical_scalar_multiply_numeric (a b : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@canonical_scalar_multiply Alg.CoreFunSem (a,b)) =
    (@toZ (WordToZ 8) a * @toZ (WordToZ 8) b) mod canonical_group_order.
Proof.
  change (@toZ (WordToZ 8) (@canonical_scalar_normalize512 Alg.CoreFunSem
    (@multiply_word_spec 8 Alg.CoreFunSem (a,b))) =
    (@toZ (WordToZ 8) a * @toZ (WordToZ 8) b) mod canonical_group_order).
  rewrite canonical_scalar_normalize512_numeric,multiply_word_spec_numeric. reflexivity.
Qed.

Lemma canonical_scalar_multiply_normalized_value (a b : Ty.tySem (Word 8)) :
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a) *
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b)) mod canonical_group_order =
  @toZ (WordToZ 8) (@canonical_scalar_multiply Alg.CoreFunSem (a,b)).
Proof.
  rewrite !canonical_scalar_normalize_numeric,canonical_scalar_multiply_numeric.
  symmetry; apply Z.mul_mod.
  pose proof canonical_group_order_range; lia.
Qed.

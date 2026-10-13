(** Literal square from LibSecp256k1.hs: duplicate the input, then multiply.
    Numeric equalities below are internal implementation bridges only. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_negate
  C.jet_secp_canonical_scalar_negate_parametric C.jet_secp_scalar_mul_literal_numeric.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition canonical_scalar_square {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  iden &&& iden >>> @canonical_scalar_multiply term.

Lemma canonical_scalar_square_parametric : Alg.Core.Parametric (@canonical_scalar_square).
Proof.
  intros term1 term2 R; unfold canonical_scalar_square.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; apply Alg.iden_Parametric.
  - apply canonical_scalar_multiply_parametric.
Qed.
Lemma canonical_scalar_square_step (value : Ty.tySem (Word 8)) :
  @canonical_scalar_square Alg.CoreFunSem value =
    @canonical_scalar_multiply Alg.CoreFunSem (value,value).
Proof. reflexivity. Qed.
Lemma canonical_scalar_square_normalized_value (value : Ty.tySem (Word 8)) :
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) *
   @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)) mod canonical_group_order =
  @toZ (WordToZ 8) (@canonical_scalar_square Alg.CoreFunSem value).
Proof. exact (canonical_scalar_multiply_normalized_value value value). Qed.

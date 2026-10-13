(** Literal canonical LibSecp256k1.gej_is_infinity = drop fe_is_zero. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Simplicity.Bit.
Require Import C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Require Import C.jet_test_value_spec C.jet_equality_spec.
Set Default Timeout 10.

Definition literal_gej_is_infinity {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Sum Ty.Unit Ty.Unit) :=
  Alg.Core.Combinators.drop (@canonical_fe_is_zero term).

Lemma canonical_fe_is_zero_parametric : Alg.Core.Parametric (@canonical_fe_is_zero).
Proof.
  intros term1 term2 R. unfold canonical_fe_is_zero.
  apply Bit.or_Parametric.
  - apply is_zero_word_spec_parametric.
  - apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Alg.scribe_Parametric].
      * apply Alg.iden_Parametric.
    + apply equality_spec_parametric.
Qed.
Lemma literal_gej_is_infinity_parametric : Alg.Core.Parametric (@literal_gej_is_infinity).
Proof.
  intros term1 term2 R. unfold literal_gej_is_infinity.
  apply Alg.drop_Parametric, canonical_fe_is_zero_parametric.
Qed.
Lemma literal_gej_is_infinity_value x y z :
  @literal_gej_is_infinity Alg.CoreFunSem ((x,y),z) =
    @canonical_fe_is_zero Alg.CoreFunSem z.
Proof. reflexivity. Qed.
Print Assumptions literal_gej_is_infinity_parametric.

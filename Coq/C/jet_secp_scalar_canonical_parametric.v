(* Canonical scalar terms inhabit the core algebra, not arbitrary functions. *)
Require Import Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_subtract_spec C.jet_test_value_spec C.jet_equality_spec.
Require Import C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_zero.
Set Default Timeout 10.

Lemma canonical_scalar_normalize_parametric : Alg.Core.Parametric (@canonical_scalar_normalize).
Proof.
  intros term1 term2 R; unfold canonical_scalar_normalize.
  repeat first [assumption | apply subtract_word_spec_parametric |
    apply Alg.scribe_Parametric | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric |
    apply Alg.unit_Parametric | apply Bit.cond_Parametric].
Qed.

Lemma canonical_scalar_is_zero_parametric : Alg.Core.Parametric (@canonical_scalar_is_zero).
Proof.
  intros term1 term2 R; unfold canonical_scalar_is_zero.
  apply Bit.or_Parametric.
  - apply is_zero_word_spec_parametric.
  - apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Alg.scribe_Parametric].
      * apply Alg.iden_Parametric.
    + apply equality_spec_parametric.
Qed.

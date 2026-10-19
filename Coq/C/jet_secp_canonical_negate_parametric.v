(** Algebra-independent literal program ports; no C coverage is registered. *)
Require Import Simplicity.Alg Simplicity.Word.
Require Import C.jet_secp_canonical_negate C.jet_multiply_spec C.jet_division_core_spec.
Set Default Timeout 10.

Lemma canonical_fe_normalize512_parametric :
  Alg.Core.Parametric (@canonical_fe_normalize512).
Proof.
  intros term1 term2 R. unfold canonical_fe_normalize512.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.iden_Parametric|].
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|].
    apply Alg.pair_Parametric; [apply Word.zero_Parametric|apply Alg.scribe_Parametric].
  - apply Alg.comp_Parametric; [apply modulo_word_spec_parametric|].
    apply Alg.drop_Parametric, Alg.iden_Parametric.
Qed.

Lemma canonical_fe_multiply_parametric : Alg.Core.Parametric (@canonical_fe_multiply).
Proof.
  intros term1 term2 R. unfold canonical_fe_multiply.
  apply Alg.comp_Parametric; [apply multiply_word_spec_parametric|
    apply canonical_fe_normalize512_parametric].
Qed.

Lemma canonical_fe_negate_parametric : Alg.Core.Parametric (@canonical_fe_negate).
Proof.
  intros term1 term2 R. unfold canonical_fe_negate.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.scribe_Parametric|apply Alg.iden_Parametric].
  - apply canonical_fe_multiply_parametric.
Qed.
Print Assumptions canonical_fe_negate_parametric.

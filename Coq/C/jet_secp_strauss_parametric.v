Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Import C.jet_secp_strauss_complete_program C.jet_secp_strauss_program
 C.jet_secp_scalar_table_literal C.jet_secp_split_literal C.jet_secp_scalar_split128_literal
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf_literal C.jet_secp_literal_infinity
 C.jet_secp_literal_gej_predicate C.jet_secp_canonical_scalar_zero
 C.jet_secp_generate_program C.jet_secp_negate_literal_contract
 C.jet_secp_rescale_literal C.jet_secp_gej_negate_parametric
 C.jet_secp_curve_literal C.jet_secp_beta_spec C.jet_secp_scalar_canonical_parametric
 C.jet_assertion_spec C.jet_test_value_spec C.jet_equality_spec
 C.jet_secp_gej_norm_literal C.jet_secp_double_literal C.jet_secp_literal_add_program
 C.jet_secp_multiply_literal_spec C.jet_literal_division_parametric.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Ltac scale_core :=
 lazymatch goal with
 | |- _ _ _ (@Alg.Core.Combinators.comp _ _ _ _ _ _) _ => apply Alg.comp_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.pair _ _ _ _ _ _) _ => apply Alg.pair_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.take _ _ _ _ _) _ => apply Alg.take_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.drop _ _ _ _ _) _ => apply Alg.drop_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.iden _ _) _ => apply Alg.iden_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.unit _ _) _ => apply Alg.unit_Parametric
 end.
Lemma scale_pass2_1_parametric : Alg.Core.Parametric (@literal_pass2_1).
Proof.
 intros a b R;unfold literal_pass2_1.
 repeat first [apply literal_gej_zinv_parametric|scale_core].
Qed.
Lemma scale_pass2_2_parametric : Alg.Core.Parametric (@literal_pass2_2).
Proof.
 intros a b R;unfold literal_pass2_2.
 repeat first [apply scale_pass2_1_parametric|apply literal_fe_multiply_parametric|scale_core].
Qed.
Lemma scale_pass2_4_parametric : Alg.Core.Parametric (@literal_pass2_4).
Proof.
 intros a b R;unfold literal_pass2_4.
 repeat first [apply scale_pass2_2_parametric|apply literal_fe_multiply_parametric|scale_core].
Qed.
Lemma scale_pass2_8_parametric : Alg.Core.Parametric (@literal_pass2_8).
Proof.
 intros a b R;unfold literal_pass2_8.
 repeat first [apply scale_pass2_4_parametric|apply literal_fe_multiply_parametric|
  apply literal_fe_one256_parametric|scale_core].
Qed.
Lemma scale_table5_parametric : Alg.Core.Parametric (@literal_scalar_table5).
Proof.
 intros a b R;unfold literal_scalar_table5.
 repeat first [apply literal_gej_double_parametric|apply literal_gej_zinv_parametric|
  apply literal_fe_multiply_parametric|apply literal_pass1_8_parametric|apply scale_pass2_8_parametric|scale_core].
Qed.
Lemma scale_split_lambda_parametric : Alg.Core.Parametric (@literal_strauss_split_lambda).
Proof.
 intros a b R;unfold literal_strauss_split_lambda,strauss_split_windows.
 repeat first [apply literal_scalar_split_lambda_parametric|apply literal_wnaf5_parametric|scale_core].
Qed.
Lemma scale_split128_parametric : Alg.Core.Parametric (@literal_strauss_split128).
Proof.
 intros a b R;unfold literal_strauss_split128,strauss_split_windows.
 repeat first [apply literal_scalar_split128_parametric|apply literal_wnaf15_parametric|scale_core].
Qed.
Lemma scale_strauss_body_parametric : Alg.Core.Parametric (@literal_strauss_body).
Proof.
 intros a b R;unfold literal_strauss_body,strauss_body_routing.
 repeat first [apply literal_gej_infinity_parametric|apply scale_table5_parametric|
  apply scale_split_lambda_parametric|apply scale_split128_parametric|
  apply literal_strauss_digits129_parametric|apply literal_fe_multiply_parametric|scale_core].
Qed.
Lemma scale_scalar_zero_parametric : Alg.Core.Parametric (@canonical_scalar_is_zero).
Proof.
 intros a b R;unfold canonical_scalar_is_zero.
 repeat first [apply Bit.or_Parametric|apply is_zero_word_spec_parametric|
  apply equality_spec_parametric|apply Alg.scribe_Parametric|scale_core].
Qed.
Lemma scale_guard_parametric : Alg.Core.Parametric (@literal_strauss_guard).
Proof.
 intros a b R;unfold literal_strauss_guard.
 repeat first [apply literal_gej_is_infinity_parametric|apply scale_scalar_zero_parametric|
  apply Bit.or_Parametric|scale_core].
Qed.
Local Opaque literal_strauss_guard literal_strauss_body literal_generate.
Lemma scale_off_curve_combination_parametric : Alg.Core.Parametric (@literal_off_curve_linear_combination_1).
Proof.
 intros a b R;unfold literal_off_curve_linear_combination_1.
 repeat first [apply Bit.cond_Parametric|apply scale_guard_parametric|
  apply literal_generate_parametric|apply scale_strauss_body_parametric|scale_core].
Qed.
Lemma scale_off_curve_parametric : Alg.Core.Parametric (@literal_off_curve_scale).
Proof.
 intros a b R;unfold literal_off_curve_scale.
 repeat first [apply scale_off_curve_combination_parametric|apply Word.zero_Parametric|scale_core].
Qed.

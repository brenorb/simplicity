(** Derive the curve guard needed by the multiplier from the actual C
    decompressor's successful square test, including its parity negation. *)
From Coq Require Import ZArith Lia Ring.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_execution C.jet_secp_rescale_literal C.jet_secp_curve_literal
 C.jet_secp_root_chain_numeric C.jet_secp_root_check C.jet_secp_decompress_numeric
 C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque root_chain_candidate decompress_root_words rescale_field_output literal_fe_add literal_fe_cube
 literal_fe_negate literal_ge_is_on_curve canonical_fe_normalize toZ.

Lemma decompress_root_success_curve w (x:Ty.tySem (Word 8)) :
 root_words_match w x -> root_check_flag (decompress_root_words w)=true ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem
   (x,rescale_field_output (root_chain_candidate (decompress_root_words w))))=true.
Proof.
 intros Match Success.
 pose proof (decompress_root_matches w x Match) as Root.
 pose proof (root_chain_candidate_matches _ _ Root) as Candidate.
 unfold root_check_flag in Success;apply Z.eqb_eq in Success.
 rewrite <-field_prime_matches_normalizer,(square_output_numeric _ (proj1 Candidate)),
   field_prime_matches_normalizer,(proj2 Root) in Success.
 rewrite literal_ge_curve_numeric,rescale_field_output_value,field_prime_matches_normalizer.
 rewrite Z.mul_mod_idemp_l,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 apply Z.eqb_eq;rewrite Success.
 unfold decompress_root_input;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,
   curve_seven_value,literal_curve_cube_numeric.
 rewrite Z.mod_mod,Z.add_mod_idemp_r by (unfold feP,feR;lia).
 rewrite Z.add_comm;reflexivity.
Qed.

Lemma decompress_negated_y_curve (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,@literal_fe_negate Alg.CoreFunSem y))=
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y)).
Proof.
 rewrite !literal_ge_curve_numeric,literal_curve_negate_numeric.
 rewrite Z.mul_mod_idemp_l,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 replace ((feP-@toZ (WordToZ 8) y)*(feP-@toZ (WordToZ 8) y)) with
   (@toZ (WordToZ 8) y*@toZ (WordToZ 8) y+(feP-2*@toZ (WordToZ 8) y)*feP) by ring.
 rewrite Z.mod_add by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma decompress_normalized_input_match w (x:Ty.tySem (Word 8)) :
 root_words_match w x -> root_words_match w (@canonical_fe_normalize Alg.CoreFunSem x).
Proof.
 intros [Bounds Residue];split;[exact Bounds|].
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model,
  Z.mod_mod by (unfold feP,feR;lia);exact Residue.
Qed.

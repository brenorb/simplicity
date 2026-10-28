(** Arbitrary inverse-Z preparation: no nonzero, inverse or on-curve premise. *)
From Coq Require Import ZArith Lia Ring.
From compcert Require Import Integers.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_point_mul_numeric C.jet_secp_curve_mul C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_execution C.jet_secp_field_mul_small C.jet_secp_field_weak_loose
 C.jet_secp_mixed_difference C.jet_secp_mixed_dispatch_literal C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_nonzero_literal C.jet_secp_field_pair_multiply C.jet_secp_zinv_start
 C.jet_secp_zinv_preparation C.jet_secp_zinv_differences C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words square_words field_pair_product weak_loose_words mixed_difference_words.

Lemma zinv_az_value z inv : square_input_bounds z -> square_input_bounds inv ->
 radix_value (zinv_az_words z inv) mod feP=(radix_value z*radix_value inv) mod feP /\
 mul_small_input_bounds (zinv_az_words z inv).
Proof.
 intros BZ BI;unfold zinv_az_words;split;[|apply double_mul_tight;assumption].
 exact (proj1 (curve_mul_value_bounds z inv (field_operand_from_bounds z BZ) (field_operand_from_bounds inv BI))).
Qed.

Lemma zinv_z12_value z inv : square_input_bounds z -> square_input_bounds inv ->
 radix_value (zinv_z12_words z inv) mod feP=
 ((radix_value z*radix_value inv)*(radix_value z*radix_value inv)) mod feP /\
 mul_small_input_bounds (zinv_z12_words z inv).
Proof.
 intros BZ BI;destruct (zinv_az_value z inv BZ BI) as [AZ BAZ].
 unfold zinv_z12_words;split;[|apply double_square_tight;apply double_tight_loose;exact BAZ].
 rewrite <-field_prime_matches_normalizer,(square_output_numeric _ (double_tight_loose _ BAZ)),field_prime_matches_normalizer.
 apply double_residue_product;exact AZ.
Qed.

Lemma zinv_u2_value u z inv : square_input_bounds u -> square_input_bounds z -> square_input_bounds inv ->
 radix_value (point_mul_words u (zinv_z12_words z inv)) mod feP=
 (radix_value u*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) mod feP /\
 mul_small_input_bounds (point_mul_words u (zinv_z12_words z inv)).
Proof.
 intros BU BZ BI;destruct (zinv_z12_value z inv BZ BI) as [Z12 B12].
 split;[|apply double_mul_tight;[exact BU|apply double_tight_loose;exact B12]].
 rewrite (proj1 (curve_mul_value_bounds u (zinv_z12_words z inv)
   (field_operand_from_bounds u BU) (field_operand_from_bounds _ (double_tight_loose _ B12)))).
 replace (radix_value u*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) with
 (radix_value u*((radix_value z*radix_value inv)*(radix_value z*radix_value inv))) by ring.
 apply double_residue_product;[reflexivity|exact Z12].
Qed.

Lemma zinv_s2_value v z inv : square_input_bounds v -> square_input_bounds z -> square_input_bounds inv ->
 radix_value (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv)) mod feP=
 (radix_value v*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) mod feP /\
 mul_small_input_bounds (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv)).
Proof.
 intros BV BZ BI;destruct (zinv_az_value z inv BZ BI) as [AZ BAZ].
 destruct (zinv_u2_value v z inv BV BZ BI) as [S2 BS2].
 unfold zinv_s2_words;destruct (mixed_pair_product_numeric (point_mul_words v (zinv_z12_words z inv))
   (zinv_az_words z inv) (double_tight_loose _ BS2) (double_tight_loose _ BAZ)) as [Value Bound].
 split;[rewrite Value;apply double_residue_product;assumption|exact Bound].
Qed.

Theorem zinv_differences_value x y z u v inv :
 (forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60) ->
 (forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60) ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value (zinv_h_words x z u inv) mod feP=
 (radix_value u*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)-radix_value x) mod feP /\
 radix_value (zinv_i_words y z v inv) mod feP=
 (radix_value y-radix_value v*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) mod feP /\
 square_input_bounds (zinv_h_words x z u inv) /\ square_input_bounds (zinv_i_words y z v inv).
Proof.
 intros BX BY BZ BU BV BI.
 destruct (weak_loose_numeric x BX) as [WX BWX];destruct (weak_loose_numeric y BY) as [WY BWY].
 destruct (zinv_u2_value u z inv BU BZ BI) as [U2 BU2].
 destruct (zinv_s2_value v z inv BV BZ BI) as [S2 BS2].
 split.
 - unfold zinv_h_words;rewrite mixed_difference_residue by assumption.
   apply mixed_residue_difference;assumption.
 - split.
   + unfold zinv_i_words;rewrite mixed_difference_residue by assumption.
     apply mixed_residue_difference;assumption.
   + split.
     * exact (proj2 (mixed_difference_numeric (weak_loose_words x) (point_mul_words u (zinv_z12_words z inv)) BWX BU2)).
     * exact (proj2 (mixed_difference_numeric (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv)) (weak_loose_words y) BS2 BWY)).
Qed.

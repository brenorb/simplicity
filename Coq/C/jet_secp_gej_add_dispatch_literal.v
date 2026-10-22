(** Actual projective preparation words and zero tests against the fixed
    finite literal-addition operands. No curve or canonical-input restriction. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_curve_mul C.jet_secp_field_mul_small C.jet_secp_mixed_difference
 C.jet_secp_double_coordinate_numeric C.jet_secp_mixed_dispatch_literal C.jet_secp_gej_add_finite_difference
 C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal C.jet_secp_canonical_normalize
 C.jet_secp_canonical_zero C.jet_secp_curve_literal C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words mixed_difference_words.

Lemma gej_add_u_residue x w a c : square_input_bounds x -> square_input_bounds w ->
 radix_value x mod feP=a mod feP -> radix_value w mod feP=c mod feP ->
 radix_value (gej_add_u1_words x w) mod feP=(a*c*c) mod feP.
Proof.
 intros BX BW HX HW;unfold gej_add_u1_words.
 rewrite (proj1 (curve_mul_value_bounds x (square_words w) (field_operand_from_bounds x BX)
   (field_operand_from_bounds _ (double_tight_loose _ (double_square_tight w BW))))).
 replace (a*c*c) with (a*(c*c)) by ring.
 apply double_residue_product;[exact HX|].
 rewrite <-field_prime_matches_normalizer,(square_output_numeric w BW),field_prime_matches_normalizer.
 apply double_residue_product;exact HW.
Qed.
Lemma gej_add_s_residue y w a c : square_input_bounds y -> square_input_bounds w ->
 radix_value y mod feP=a mod feP -> radix_value w mod feP=c mod feP ->
 radix_value (gej_add_s1_words y w) mod feP=(a*c*c*c) mod feP.
Proof.
 intros BY BW HY HW;unfold gej_add_s1_words.
 rewrite (proj1 (curve_mul_value_bounds (point_mul_words y (square_words w)) w
   (field_operand_from_bounds _ (double_tight_loose _
     (double_mul_tight y (square_words w) BY (double_tight_loose _ (double_square_tight w BW)))))
   (field_operand_from_bounds w BW))).
 apply double_residue_product;[apply gej_add_u_residue;assumption|exact HW].
Qed.

Lemma gej_add_h_bounds x z u w : square_input_bounds x -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds w -> square_input_bounds (gej_add_h_words x z u w).
Proof.
 intros BX BZ BU BW;unfold gej_add_h_words,gej_add_u1_words,gej_add_u2_words.
 apply (proj2 (mixed_difference_numeric _ _
   (double_mul_tight x (square_words w) BX (double_tight_loose _ (double_square_tight w BW)))
   (double_mul_tight u (square_words z) BU (double_tight_loose _ (double_square_tight z BZ))))).
Qed.
Lemma gej_add_i_bounds y z v w : square_input_bounds y -> square_input_bounds z ->
 square_input_bounds v -> square_input_bounds w -> square_input_bounds (gej_add_i_words y z v w).
Proof.
 intros BY BZ BV BW;unfold gej_add_i_words,gej_add_s1_words,gej_add_s2_words.
 apply (proj2 (mixed_difference_numeric _ _
   (double_mul_tight (point_mul_words v (square_words z)) z
     (double_tight_loose _ (double_mul_tight v (square_words z) BV (double_tight_loose _ (double_square_tight z BZ)))) BZ)
   (double_mul_tight (point_mul_words y (square_words w)) w
     (double_tight_loose _ (double_mul_tight y (square_words w) BY (double_tight_loose _ (double_square_tight w BW)))) BW))).
Qed.
Lemma gej_add_h_residue x z u w a c b d :
 square_input_bounds x -> square_input_bounds z -> square_input_bounds u -> square_input_bounds w ->
 radix_value x mod feP=a mod feP -> radix_value z mod feP=c mod feP ->
 radix_value u mod feP=b mod feP -> radix_value w mod feP=d mod feP ->
 radix_value (gej_add_h_words x z u w) mod feP=(b*c*c-a*d*d) mod feP.
Proof.
 intros BX BZ BU BW HX HZ HU HW;unfold gej_add_h_words.
 rewrite mixed_difference_residue.
 - apply mixed_residue_difference;apply gej_add_u_residue;assumption.
 - unfold gej_add_u1_words;apply double_mul_tight;[exact BX|apply double_tight_loose;apply double_square_tight;exact BW].
 - unfold gej_add_u2_words;apply double_mul_tight;[exact BU|apply double_tight_loose;apply double_square_tight;exact BZ].
Qed.
Lemma gej_add_i_residue y z v w a c b d :
 square_input_bounds y -> square_input_bounds z -> square_input_bounds v -> square_input_bounds w ->
 radix_value y mod feP=a mod feP -> radix_value z mod feP=c mod feP ->
 radix_value v mod feP=b mod feP -> radix_value w mod feP=d mod feP ->
 radix_value (gej_add_i_words y z v w) mod feP=(a*d*d*d-b*c*c*c) mod feP.
Proof.
 intros BY BZ BV BW HY HZ HV HW;unfold gej_add_i_words.
 rewrite mixed_difference_residue.
 - apply mixed_residue_difference;apply gej_add_s_residue;assumption.
 - unfold gej_add_s2_words;apply double_mul_tight;[|exact BZ].
   apply double_tight_loose;apply double_mul_tight;[exact BV|apply double_tight_loose;apply double_square_tight;exact BZ].
 - unfold gej_add_s1_words;apply double_mul_tight;[|exact BW].
   apply double_tight_loose;apply double_mul_tight;[exact BY|apply double_tight_loose;apply double_square_tight;exact BW].
Qed.

Definition gej_add_literal_u (a d : Ty.tySem (Word 8)) :=
 @literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_square Alg.CoreFunSem d).
Definition gej_add_literal_s (a d : Ty.tySem (Word 8)) :=
 @literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_cube Alg.CoreFunSem d).
Definition gej_add_literal_h (a c b d : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem
  (gej_add_literal_u a d,gej_add_literal_u (@literal_fe_negate Alg.CoreFunSem b) c).
Definition gej_add_literal_i (a c b d : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem
  (gej_add_literal_s a d,gej_add_literal_s (@literal_fe_negate Alg.CoreFunSem b) c).
Lemma gej_add_literal_u_numeric a d : @toZ (WordToZ 8) (gej_add_literal_u a d)=
 (@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d) mod feP.
Proof.
 unfold gej_add_literal_u;rewrite literal_multiply_numeric,literal_square_numeric,Z.mul_mod_idemp_r
   by (unfold feP,feR;lia);f_equal;ring.
Qed.
Lemma gej_add_literal_s_numeric a d : @toZ (WordToZ 8) (gej_add_literal_s a d)=
 (@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d) mod feP.
Proof.
 unfold gej_add_literal_s;rewrite literal_multiply_numeric,literal_curve_cube_numeric,Z.mul_mod_idemp_r
   by (unfold feP,feR;lia);f_equal;ring.
Qed.
Lemma gej_add_literal_h_numeric a c b d : @toZ (WordToZ 8) (gej_add_literal_h a c b d)=
 (@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
  @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP.
Proof.
 unfold gej_add_literal_h,gej_add_literal_u;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,
   !literal_multiply_numeric,!literal_square_numeric,literal_curve_negate_numeric.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) a*(@toZ (WordToZ 8) d*@toZ (WordToZ 8) d)+
   (feP-@toZ (WordToZ 8) b)*(@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) with
  ((@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
    @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)+
    (@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)*feP) by ring.
 apply Z.mod_add;unfold feP,feR;lia.
Qed.
Lemma gej_add_literal_i_numeric a c b d : @toZ (WordToZ 8) (gej_add_literal_i a c b d)=
 (@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
  @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP.
Proof.
 unfold gej_add_literal_i,gej_add_literal_s;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,
   !literal_multiply_numeric,!literal_curve_cube_numeric,literal_curve_negate_numeric.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) a*(@toZ (WordToZ 8) d*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d)+
   (feP-@toZ (WordToZ 8) b)*(@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) with
  ((@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
    @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)+
    (@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)*feP) by ring.
 apply Z.mod_add;unfold feP,feR;lia.
Qed.

Lemma gej_add_h_reader_residue (a c b d : Ty.tySem (Word 8)) :
 radix_value (gej_add_h_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b) (square_reader_rho d)) mod feP=
 (-@toZ (WordToZ 8) (gej_add_literal_h a c b d)) mod feP.
Proof.
 rewrite gej_add_literal_h_numeric.
 change (radix_value (gej_add_h_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b) (square_reader_rho d)) mod feP=
   (0-(@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
   @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP) mod feP).
 rewrite Zminus_mod_idemp_r.
 replace (0-(@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
   @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) with
  (@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c-
   @toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d) by ring.
 apply gej_add_h_residue;try apply square_reader_bounds;
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.
Lemma gej_add_i_reader_residue (a c b d : Ty.tySem (Word 8)) :
 radix_value (gej_add_i_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b) (square_reader_rho d)) mod feP=
 @toZ (WordToZ 8) (gej_add_literal_i a c b d) mod feP.
Proof.
 rewrite gej_add_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply gej_add_i_residue;try apply square_reader_bounds;
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.
Lemma gej_add_u_reader_residue (a d : Ty.tySem (Word 8)) :
 radix_value (gej_add_u1_words (square_reader_rho a) (square_reader_rho d)) mod feP=
 @toZ (WordToZ 8) (gej_add_literal_u a d) mod feP.
Proof.
 rewrite gej_add_literal_u_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply gej_add_u_residue;try apply square_reader_bounds;
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.
Lemma gej_add_s_reader_residue (a d : Ty.tySem (Word 8)) :
 radix_value (gej_add_s1_words (square_reader_rho a) (square_reader_rho d)) mod feP=
 @toZ (WordToZ 8) (gej_add_literal_s a d) mod feP.
Proof.
 rewrite gej_add_literal_s_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply gej_add_s_residue;try apply square_reader_bounds;
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.
Theorem gej_add_h_reader_test (a c b d : Ty.tySem (Word 8)) :
 Z.eqb (radix_value (gej_add_h_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b) (square_reader_rho d)) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h a c b d)).
Proof. rewrite gej_add_h_reader_residue,literal_curve_zero_numeric;apply mixed_negated_zero_test. Qed.
Theorem gej_add_i_reader_test (a c b d : Ty.tySem (Word 8)) :
 Z.eqb (radix_value (gej_add_i_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b) (square_reader_rho d)) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_i a c b d)).
Proof. rewrite gej_add_i_reader_residue,literal_curve_zero_numeric;reflexivity. Qed.

(** Actual nonzero-H machine coordinates against the fixed literal expression. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_curve_mul C.jet_secp_field_mul_small C.jet_secp_field_sum_bounds C.jet_secp_field_add_scaled
 C.jet_secp_field_negate_separate C.jet_secp_mixed_nonzero_products C.jet_secp_mixed_nonzero_tail
 C.jet_secp_mixed_x_tail C.jet_secp_mixed_y_tail C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_dispatch_literal C.jet_secp_square_execution C.jet_secp_curve_literal
 C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_canonical_normalize C.jet_secp_double_literal C.jet_secp_negate_literal_contract
 C.jet_secp_rescale_literal C.jet_secp_double_literal_bridge C.jet_secp_field_pair_multiply
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_double_half_literal_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words negate_sep_words field_pair_product rescale_field_output
 literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube literal_fe_negate literal_fe_multiply_int.

Lemma mixed_square_negative h a : square_input_bounds h -> radix_value h mod feP=(-a) mod feP ->
 radix_value (square_words h) mod feP=(a*a) mod feP.
Proof.
 intros BH HH;rewrite <-field_prime_matches_normalizer,(square_output_numeric h BH),field_prime_matches_normalizer.
 replace (a*a) with ((-a)*(-a)) by ring;apply double_residue_product;exact HH.
Qed.

Local Transparent field_pair_product.
Lemma mixed_pair_product_numeric a b : square_input_bounds a -> square_input_bounds b ->
 radix_value (field_pair_product a b) mod feP=(radix_value a*radix_value b) mod feP /\
 mul_small_input_bounds (field_pair_product a b).
Proof.
 intros BA BB;pose proof (field_pair_input_bounds a b BA BB) as BI;split.
 - unfold field_pair_product;rewrite <-field_prime_matches_normalizer,(original_outputs_product _ BI),
     field_pair_radix_left,field_pair_radix_right;reflexivity.
 - intros j HJ;unfold field_pair_product;exact (proj2 (original_outputs_bounds _ BI j HJ)).
Qed.
Local Opaque field_pair_product.
Lemma mixed_products_match h u a c : square_input_bounds h -> square_input_bounds u ->
 radix_value h mod feP=(-a) mod feP -> radix_value u mod feP=c mod feP ->
 radix_value (mixed_h3_words h) mod feP=(a*a*a) mod feP /\
 radix_value (mixed_t_words u h) mod feP=(-(c*a*a)) mod feP /\
 mul_small_input_bounds (mixed_h3_words h) /\ mul_small_input_bounds (mixed_t_words u h).
Proof.
 intros BH BU HH HU.
 pose proof (negate_sep_numeric (square_words h) (double_square_tight h BH)) as [VN BN].
 assert (HN : radix_value (mixed_h2_words h) mod feP=(-(a*a)) mod feP).
 { unfold mixed_h2_words;rewrite VN.
   replace (4*feP-radix_value (square_words h)) with ((0-radix_value (square_words h))+4*feP) by ring.
   rewrite Z.mod_add by (unfold feP,feR;lia).
   change ((0-radix_value (square_words h)) mod feP=(0-a*a) mod feP).
   apply mixed_residue_difference;[reflexivity|apply mixed_square_negative;assumption]. }
 split.
 - unfold mixed_h3_words;rewrite (proj1 (curve_mul_value_bounds (mixed_h2_words h) h
     (field_operand_from_bounds _ BN) (field_operand_from_bounds h BH))).
   replace (a*a*a) with ((-(a*a))*(-a)) by ring;apply double_residue_product;assumption.
 - split.
   + unfold mixed_t_words;rewrite (proj1 (curve_mul_value_bounds u (mixed_h2_words h)
       (field_operand_from_bounds u BU) (field_operand_from_bounds _ BN))).
     replace (-(c*a*a)) with (c*(-(a*a))) by ring;apply double_residue_product;assumption.
   + split;[unfold mixed_h3_words|unfold mixed_t_words];apply double_mul_tight;assumption.
Qed.

Definition mixed_literal_t (a c : Ty.tySem (Word 8)) :=
 @literal_fe_multiply Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem a,c).
Definition mixed_literal_rx (a b c : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem
  (@literal_fe_add Alg.CoreFunSem (@literal_fe_cube Alg.CoreFunSem a,
    @literal_fe_multiply_int (-2) Alg.CoreFunSem (mixed_literal_t a c)),@literal_fe_square Alg.CoreFunSem b).
Definition mixed_literal_tx (a b c : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem (mixed_literal_rx a b c,@literal_fe_negate Alg.CoreFunSem (mixed_literal_t a c)).
Definition mixed_literal_ry (a b c d : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem
  (@literal_fe_multiply Alg.CoreFunSem (@literal_fe_cube Alg.CoreFunSem a,d),
   @literal_fe_multiply Alg.CoreFunSem (b,mixed_literal_tx a b c)).
Definition mixed_literal_rz (a e : Ty.tySem (Word 8)) :=
 @literal_fe_multiply Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (a,e),
   @literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)).
Lemma mixed_literal_rx_numeric a b c : @toZ (WordToZ 8) (mixed_literal_rx a b c)=
 (@toZ (WordToZ 8) b*@toZ (WordToZ 8) b+@toZ (WordToZ 8) a*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a+
  2*(-(@toZ (WordToZ 8) c*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a))) mod feP.
Proof.
 unfold mixed_literal_rx,mixed_literal_t.
 rewrite !literal_fe_add_numeric,canonical_field_order_matches_limb_model,literal_fe_multiply_int_numeric,
  literal_curve_cube_numeric,literal_multiply_numeric,!literal_square_numeric.
 repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) b*@toZ (WordToZ 8) b+@toZ (WordToZ 8) a*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a+
   2*(-(@toZ (WordToZ 8) c*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a))) with
  ((@toZ (WordToZ 8) a*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a)+
   (-2*(@toZ (WordToZ 8) a*@toZ (WordToZ 8) a*@toZ (WordToZ 8) c))+@toZ (WordToZ 8) b*@toZ (WordToZ 8) b) by ring.
 apply double_residue_sum;[apply double_residue_sum|];
   repeat rewrite Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma mixed_x_matches_literal h i u (a b c : Ty.tySem (Word 8)) :
 square_input_bounds h -> square_input_bounds i -> square_input_bounds u ->
 radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP ->
 radix_value i mod feP=@toZ (WordToZ 8) b mod feP -> radix_value u mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value (mixed_nonzero_x_words h i u) mod feP=@toZ (WordToZ 8) (mixed_literal_rx a b c).
Proof.
 intros BH BI BU HH HI HU.
 destruct (mixed_products_match h u _ _ BH BU HH HU) as (HG & HT & BG & BT).
 destruct (mixed_x_bounds i (mixed_h3_words h) (mixed_t_words u h) BI BG BT) as (BX & BTT & VX & VT).
 unfold mixed_nonzero_x_words;rewrite VX,mixed_literal_rx_numeric.
 apply double_residue_sum.
 - apply double_residue_sum;[|exact HG].
   rewrite <-field_prime_matches_normalizer,(square_output_numeric i BI),field_prime_matches_normalizer.
   apply double_residue_product;exact HI.
 - apply double_residue_product;[reflexivity|exact HT].
Qed.

Lemma mixed_literal_neg_t_numeric a c :
 @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem (mixed_literal_t a c))=
 (-(@toZ (WordToZ 8) c*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a)) mod feP.
Proof.
 unfold mixed_literal_t;rewrite literal_curve_negate_numeric,literal_multiply_numeric,literal_square_numeric,
   Z.mul_mod_idemp_l,Zminus_mod_idemp_r by (unfold feP,feR;lia).
 replace (feP-@toZ (WordToZ 8) a*@toZ (WordToZ 8) a*@toZ (WordToZ 8) c) with
  ((-(@toZ (WordToZ 8) c*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a))+1*feP) by ring.
 apply Z.mod_add;unfold feP,feR;lia.
Qed.
Lemma mixed_tx_matches_literal h i u (a b c : Ty.tySem (Word 8)) :
 square_input_bounds h -> square_input_bounds i -> square_input_bounds u ->
 radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP ->
 radix_value i mod feP=@toZ (WordToZ 8) b mod feP -> radix_value u mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value (mixed_tx_words i (mixed_h3_words h) (mixed_t_words u h)) mod feP=
 @toZ (WordToZ 8) (mixed_literal_tx a b c).
Proof.
 intros BH BI BU HH HI HU.
 destruct (mixed_products_match h u _ _ BH BU HH HU) as (HG & HT & BG & BT).
 destruct (mixed_x_bounds i (mixed_h3_words h) (mixed_t_words u h) BI BG BT) as (BX & BTT & VX & VT).
 unfold mixed_tx_words;rewrite (field_sum_exact_value _ _
  (field_sum_scaled_no_overflow 1 4 _ _ ltac:(lia) ltac:(lia) ltac:(lia) (field_tight_scaled _ BT) BX)).
 unfold mixed_literal_tx;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model.
 rewrite Z.add_comm;apply double_residue_sum.
 - apply double_match_mod;apply mixed_x_matches_literal;assumption.
 - rewrite mixed_literal_neg_t_numeric,Z.mod_mod by (unfold feP,feR;lia);exact HT.
Qed.

Lemma mixed_y_matches_literal h i u s (a b c d : Ty.tySem (Word 8)) :
 square_input_bounds h -> square_input_bounds i -> square_input_bounds u -> square_input_bounds s ->
 radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP -> radix_value i mod feP=@toZ (WordToZ 8) b mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) c mod feP -> radix_value s mod feP=@toZ (WordToZ 8) d mod feP ->
 radix_value (mixed_nonzero_y_words h i u s) mod feP=@toZ (WordToZ 8) (mixed_literal_ry a b c d).
Proof.
 intros BH BI BU BS HH HI HU HS.
 destruct (mixed_products_match h u _ _ BH BU HH HU) as (HG & HT & BG & BT).
 pose proof (double_tight_loose _ BG) as BGL.
 destruct (mixed_x_bounds i (mixed_h3_words h) (mixed_t_words u h) BI BG BT) as (BX & BTT & VX & VT).
 pose proof (field_scaled_loose 5 _ ltac:(lia) BTT) as BTL.
 pose proof (double_mul_tight _ i BTL BI) as BP.
 destruct (mixed_pair_product_numeric _ s BGL BS) as [VP BGP].
 unfold mixed_nonzero_y_words,mixed_y_words;rewrite (field_sum_exact_value _ _
  (field_sum_scaled_no_overflow 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia)
   (field_tight_scaled _ BP) (field_tight_scaled _ BGP))).
 unfold mixed_literal_ry;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model.
 rewrite Z.add_comm;apply double_residue_sum.
 - rewrite VP,literal_multiply_numeric,Z.mod_mod by (unfold feP,feR;lia).
   apply double_residue_product;[|exact HS].
   rewrite literal_curve_cube_numeric,Z.mod_mod by (unfold feP,feR;lia);exact HG.
 - rewrite (proj1 (curve_mul_value_bounds _ i (field_operand_from_bounds _ BTL) (field_operand_from_bounds i BI))),
    literal_multiply_numeric,Z.mod_mod by (unfold feP,feR;lia).
   rewrite Z.mul_comm;apply double_residue_product;[exact HI|].
   apply double_match_mod;apply mixed_tx_matches_literal;assumption.
Qed.
Lemma mixed_z_matches_literal z h (a e : Ty.tySem (Word 8)) :
 square_input_bounds z -> square_input_bounds h -> radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) e mod feP ->
 radix_value (point_mul_words z h) mod feP=@toZ (WordToZ 8) (mixed_literal_rz a e).
Proof.
 intros BZ BH HH HZ.
 unfold mixed_literal_rz;rewrite !literal_multiply_numeric,literal_curve_negate_numeric,literal_fe_one256_value.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) a*@toZ (WordToZ 8) e*(feP-1)) with
  ((@toZ (WordToZ 8) e*(-@toZ (WordToZ 8) a))+(@toZ (WordToZ 8) a*@toZ (WordToZ 8) e)*feP) by ring.
 rewrite Z.mod_add by (unfold feP,feR;lia).
 rewrite (proj1 (curve_mul_value_bounds z h (field_operand_from_bounds z BZ) (field_operand_from_bounds h BH))).
 apply double_residue_product;assumption.
Qed.

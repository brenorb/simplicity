(** Composable residue and bound bridges for the actual doubling word outputs. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Ty.
Require Import C.jet_secp_fe_math C.jet_secp_field_mul_small C.jet_secp_field_half
  C.jet_secp_field_half_numeric C.jet_secp_field_sum_bounds C.jet_secp_field_add_scaled
  C.jet_secp_field_negate_separate C.jet_secp_point_y_negate2 C.jet_secp_point_mul_storage
  C.jet_secp_point_mul_numeric C.jet_secp_curve_mul C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_square_execution C.jet_secp_curve_literal C.jet_secp_negate_literal_contract
  C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
  C.jet_secp_canonical_normalize C.jet_secp_double_literal C.jet_secp_double_half_literal_numeric
  C.jet_secp_double_half_bridge C.jet_secp_double_l_scale C.jet_secp_double_middle
  C.jet_secp_double_accumulate C.jet_secp_double_y_tail C.jet_secp_double_all_calls
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words double_l_words double_t_words double_y_words
  literal_fe_square literal_fe_multiply literal_fe_multiply_int literal_fe_halve literal_fe_add literal_fe_negate.

Lemma double_square_tight w : square_input_bounds w -> mul_small_input_bounds (square_words w).
Proof. intros HB i HI;exact (proj2 (square_output_bounds w HB i HI)). Qed.
Lemma double_tight_loose w : mul_small_input_bounds w -> square_input_bounds w.
Proof. intro HB;apply (field_scaled_loose 1 w ltac:(lia));apply field_tight_scaled;exact HB. Qed.
Lemma double_mul_tight w v : square_input_bounds w -> square_input_bounds v -> mul_small_input_bounds (point_mul_words w v).
Proof.
  intros BW BV;exact (proj2 (curve_mul_value_bounds w v
    (field_operand_from_bounds w BW) (field_operand_from_bounds v BV))).
Qed.
Local Transparent double_l_words.
Lemma double_l_bounds w : mul_small_input_bounds w -> square_input_bounds (double_l_words w).
Proof.
  intro HB;unfold double_l_words;apply half_output_reusable.
  apply mul_small_output_bounds;[change (0<=3<=7);lia|exact HB].
Qed.
Local Opaque double_l_words.
Lemma double_residue_product u v a b : u mod feP=a mod feP -> v mod feP=b mod feP ->
  (u*v) mod feP=(a*b) mod feP.
Proof.
  intros HU HV;rewrite (Z.mul_mod u v feP) by (unfold feP,feR;lia).
  rewrite HU,HV;rewrite <-Z.mul_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma double_residue_sum u v a b : u mod feP=a mod feP -> v mod feP=b mod feP ->
  (u+v) mod feP=(a+b) mod feP.
Proof.
  intros HU HV;rewrite (Z.add_mod u v feP) by (unfold feP,feR;lia).
  rewrite HU,HV;rewrite <-Z.add_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma double_residue_negate k u a : u mod feP=a mod feP ->
  (k*feP-u) mod feP=(feP-a) mod feP.
Proof.
  intro HU;rewrite (Zminus_mod (k*feP) u feP),(Zminus_mod feP a feP),
    (Z.mod_mul k feP),Z.mod_same by (unfold feP,feR;lia).
  rewrite HU;reflexivity.
Qed.
Lemma double_square_matches w (a : Ty.tySem (Word 8)) :
  square_input_bounds w -> radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value (square_words w) mod feP=@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem a).
Proof.
  intros HB HI;pose proof (square_output_numeric w HB) as HS.
  rewrite field_prime_matches_normalizer in HS;rewrite HS,literal_square_numeric.
  apply double_residue_product;exact HI.
Qed.
Lemma double_mul_matches w v (a b : Ty.tySem (Word 8)) :
  square_input_bounds w -> square_input_bounds v ->
  radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value v mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value (point_mul_words w v) mod feP=@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (a,b)).
Proof.
  intros BW BV HW HV.
  rewrite (proj1 (curve_mul_value_bounds w v (field_operand_from_bounds w BW) (field_operand_from_bounds v BV))),
    literal_multiply_numeric.
  apply double_residue_product;assumption.
Qed.
Lemma double_negate_sep_matches w (a : Ty.tySem (Word 8)) :
  mul_small_input_bounds w -> radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value (negate_sep_words w) mod feP=@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem a).
Proof.
  intros HB HI;rewrite (proj1 (negate_sep_numeric w HB)),literal_curve_negate_numeric.
  apply double_residue_negate;exact HI.
Qed.
Lemma double_sum_matches n m w v (a b : Ty.tySem (Word 8)) :
  0<=n -> 0<=m -> n+m<=8 -> field_scaled_bounds n w -> field_scaled_bounds m v ->
  radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value v mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value (field_sum_words w v) mod feP=@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (a,b)).
Proof.
  intros HN HM HNM BW BV HW HV.
  rewrite (field_sum_exact_value w v (field_sum_scaled_no_overflow n m w v HN HM HNM BW BV)),
    literal_fe_add_numeric,canonical_field_order_matches_limb_model.
  apply double_residue_sum;assumption.
Qed.

Lemma double_match_mod u (a : Ty.tySem (Word 8)) :
  u mod feP=@toZ (WordToZ 8) a -> u mod feP=@toZ (WordToZ 8) a mod feP.
Proof. intro HE;rewrite <-HE,Z.mod_mod by (unfold feP,feR;lia);reflexivity. Qed.

Lemma double_x_accum_matches u t (a b : Ty.tySem (Word 8)) :
  mul_small_input_bounds u -> mul_small_input_bounds t ->
  radix_value u mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value t mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value (double_x_accum_words u t) mod feP=@toZ (WordToZ 8)
    (@literal_fe_add Alg.CoreFunSem (@literal_fe_multiply_int 2 Alg.CoreFunSem b,a)).
Proof.
  intros BU BT HU HT;unfold double_x_accum_words.
  rewrite (proj1 (field_sum_twice_value u t BU BT)),literal_fe_add_numeric,
    canonical_field_order_matches_limb_model,literal_fe_multiply_int_numeric.
  rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
  replace (radix_value u+2*radix_value t) with (2*radix_value t+radix_value u) by ring.
  apply double_residue_sum.
  { apply double_residue_product;[reflexivity|exact HT]. }
  { exact HU. }
Qed.
Lemma double_t_accum_matches u t (a b : Ty.tySem (Word 8)) :
  mul_small_input_bounds u -> mul_small_input_bounds t ->
  radix_value u mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value t mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value (double_t_accum_words u t) mod feP=@toZ (WordToZ 8)
    (@literal_fe_add Alg.CoreFunSem
      (@literal_fe_add Alg.CoreFunSem (@literal_fe_multiply_int 2 Alg.CoreFunSem b,a),b)).
Proof.
  intros BU BT HU HT.
  pose proof (proj2 (field_sum_twice_value u t BU BT)) as BX.
  change (field_scaled_bounds 3 (double_x_accum_words u t)) in BX.
  unfold double_t_accum_words.
  rewrite (field_sum_exact_value t (double_x_accum_words u t)
    (field_sum_scaled_no_overflow 1 3 _ _ ltac:(lia) ltac:(lia) ltac:(lia) (field_tight_scaled t BT) BX)),
    literal_fe_add_numeric,canonical_field_order_matches_limb_model.
  replace (radix_value t+radix_value (double_x_accum_words u t)) with
    (radix_value (double_x_accum_words u t)+radix_value t) by ring.
  apply double_residue_sum;[apply double_match_mod;apply double_x_accum_matches;assumption|exact HT].
Qed.

Local Transparent double_y_words.
Lemma double_y_words_matches t l s (a b c : Ty.tySem (Word 8)) :
  square_input_bounds t -> square_input_bounds l -> mul_small_input_bounds s ->
  radix_value t mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value l mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value s mod feP=@toZ (WordToZ 8) c mod feP ->
  radix_value (double_y_words t l s) mod feP=@toZ (WordToZ 8)
    (@literal_fe_negate Alg.CoreFunSem
      (@literal_fe_add Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (b,a),c))).
Proof.
  intros BT BL BS HT HL HS.
  pose proof (double_mul_tight t l BT BL) as BP.
  pose proof (field_sum_scaled_bounds 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia)
    (field_tight_scaled _ BP) (field_tight_scaled _ BS)) as BSum.
  unfold double_y_words;rewrite (proj1 (point_y_neg2_numeric _ BSum)),literal_curve_negate_numeric.
  apply double_residue_negate;apply double_match_mod.
  apply double_sum_matches with (n:=1) (m:=1);
    [lia|lia|lia|apply field_tight_scaled;exact BP|apply field_tight_scaled;exact BS| |exact HS].
  apply double_match_mod.
  rewrite (proj1 (curve_mul_value_bounds t l (field_operand_from_bounds t BT) (field_operand_from_bounds l BL))),
    literal_multiply_numeric.
  replace (@toZ (WordToZ 8) b*@toZ (WordToZ 8) a) with (@toZ (WordToZ 8) a*@toZ (WordToZ 8) b) by ring.
  apply double_residue_product;assumption.
Qed.
Local Opaque double_y_words.

Local Transparent double_t_words.
Theorem double_body_coordinates_match x y z (a b c : Ty.tySem (Word 8)) :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value y mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
  let result := @literal_gej_double_body Alg.CoreFunSem ((a,b),c) in
  radix_value (double_output_x_words x y) mod feP=@toZ (WordToZ 8) (fst (fst result)) /\
  radix_value (double_output_y_words x y) mod feP=@toZ (WordToZ 8) (snd (fst result)) /\
  radix_value (double_output_z_words y z) mod feP=@toZ (WordToZ 8) (snd result).
Proof.
  intros BX BY BZ HX HY HZ;cbn zeta;rewrite literal_gej_double_body_step;cbn zeta;cbn [fst snd].
  set (sw:=square_words y);set (lw:=double_l_words (square_words x)).
  set (tw:=double_t_words x sw);set (uw:=square_words lw).
  set (sv:=@literal_fe_square Alg.CoreFunSem b).
  set (lv:=@literal_fe_halve Alg.CoreFunSem (@literal_fe_multiply_int 3 Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem a))).
  set (tv:=@literal_fe_negate Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (sv,a))).
  set (rx:=@literal_fe_add Alg.CoreFunSem (@literal_fe_multiply_int 2 Alg.CoreFunSem tv,@literal_fe_square Alg.CoreFunSem lv)).
  fold sw lw tw uw sv lv tv rx.
  assert (BS : mul_small_input_bounds sw) by (apply double_square_tight;exact BY).
  assert (BSL : square_input_bounds sw) by (apply double_tight_loose;exact BS).
  assert (BL : square_input_bounds lw) by (apply double_l_bounds;apply double_square_tight;exact BX).
  destruct (negate_sep_numeric sw BS) as [VN BN].
  assert (BT : mul_small_input_bounds tw) by (unfold tw,double_t_words;apply double_mul_tight;assumption).
  assert (BTL : square_input_bounds tw) by (apply double_tight_loose;exact BT).
  assert (BU : mul_small_input_bounds uw) by (apply double_square_tight;exact BL).
  assert (HS : radix_value sw mod feP=@toZ (WordToZ 8) sv) by (apply double_square_matches;assumption).
  assert (HL : radix_value lw mod feP=@toZ (WordToZ 8) lv).
  { apply double_l_words_matches_literal;[apply double_square_tight;exact BX|].
    apply double_match_mod;apply double_square_matches;assumption. }
  assert (HT : radix_value tw mod feP=@toZ (WordToZ 8) tv).
  { unfold tw,double_t_words.
    rewrite (proj1 (curve_mul_value_bounds (negate_sep_words sw) x (field_operand_from_bounds _ BN)
      (field_operand_from_bounds _ BX))),VN.
    unfold tv;rewrite literal_curve_negate_numeric,literal_multiply_numeric,Zminus_mod_idemp_r.
    replace ((4*feP-radix_value sw)*radix_value x) with
      ((4*radix_value x)*feP-radix_value sw*radix_value x) by ring.
    apply double_residue_negate;apply double_residue_product;
      [apply double_match_mod;exact HS|exact HX]. }
  assert (HU : radix_value uw mod feP=@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem lv)).
  { apply double_square_matches;[exact BL|apply double_match_mod;exact HL]. }
  assert (HRX : radix_value (double_x_accum_words uw tw) mod feP=@toZ (WordToZ 8) rx).
  { apply double_x_accum_matches;[exact BU|exact BT|apply double_match_mod;exact HU|apply double_match_mod;exact HT]. }
  assert (HRT : radix_value (double_t_accum_words uw tw) mod feP=@toZ (WordToZ 8)
      (@literal_fe_add Alg.CoreFunSem (rx,tv))).
  { apply double_t_accum_matches;[exact BU|exact BT|apply double_match_mod;exact HU|apply double_match_mod;exact HT]. }
  assert (BXX : field_scaled_bounds 3 (double_x_accum_words uw tw))
    by (exact (proj2 (field_sum_twice_value uw tw BU BT))).
  assert (BTT : square_input_bounds (double_t_accum_words uw tw)).
  { apply (field_scaled_loose 4 _ ltac:(lia));unfold double_t_accum_words.
    exact (field_sum_scaled_bounds 1 3 _ _ ltac:(lia) ltac:(lia) ltac:(lia) (field_tight_scaled _ BT) BXX). }
  assert (HSS : radix_value (square_words sw) mod feP=@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem sv)).
  { apply double_square_matches;[exact BSL|apply double_match_mod;exact HS]. }
  change (radix_value (double_x_accum_words uw tw) mod feP=@toZ (WordToZ 8) rx /\
    radix_value (double_y_words (double_t_accum_words uw tw) lw (square_words sw)) mod feP=
      @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem
        (@literal_fe_add Alg.CoreFunSem
          (@literal_fe_multiply Alg.CoreFunSem (lv,@literal_fe_add Alg.CoreFunSem (rx,tv)),@literal_fe_square Alg.CoreFunSem sv))) /\
    radix_value (point_mul_words z y) mod feP=@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (b,c))).
  split;[exact HRX|];split.
  - apply double_y_words_matches;
      [exact BTT|exact BL|apply double_square_tight;exact BSL|
       apply double_match_mod;exact HRT|apply double_match_mod;exact HL|apply double_match_mod;exact HSS].
  - rewrite (proj1 (curve_mul_value_bounds z y (field_operand_from_bounds _ BZ) (field_operand_from_bounds _ BY))),
      literal_multiply_numeric.
    replace (@toZ (WordToZ 8) b*@toZ (WordToZ 8) c) with (@toZ (WordToZ 8) c*@toZ (WordToZ 8) b) by ring.
    apply double_residue_product;assumption.
Qed.

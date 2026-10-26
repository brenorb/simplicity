(** The actual mixed-addition ratio on matching loose field limbs. Only the
    ratio projection is normalized when comparing with the fixed extended
    program: its reported raw equal-point-Y discrepancy is not erased. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_mixed_ex_literal_bridge C.jet_secp_mixed_xy_literal C.jet_secp_mixed_body_ratio_slice
 C.jet_secp_mixed_finite_ratio_slice C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_zero_return
 C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_nonzero_literal C.jet_secp_mixed_difference
 C.jet_secp_point_set_bit C.jet_secp_mixed_infinite_literal C.jet_secp_literal_infinity
 C.jet_secp_literal_gej_predicate C.jet_secp_canonical_zero C.jet_secp_canonical_normalize
 C.jet_secp_rescale_literal C.jet_secp_multiply_literal_spec C.jet_secp_curve_literal
 C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_add_literal C.jet_secp_add_literal_step C.jet_secp_mixed_finite_prefix
 C.jet_secp_field_mul_small C.jet_secp_double_literal_bridge C.jet_secp_mixed_finite_return.
Require Import C.jet_secp_mixed_body_loose.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque rescale_field_output literal_gej_ge_add_ex literal_gej_add_ex literal_gej_is_infinity
 canonical_fe_is_zero canonical_fe_normalize literal_fe_zero256 literal_fe_one256
 literal_fe_multiply literal_fe_negate.

Lemma mixed_ratio_clear_output : rescale_field_output (point_set_bit_words false)=
 @literal_fe_zero256 Alg.CoreFunSem tt.
Proof.
 rewrite <-zero_field_writer_literal_output;apply (toZ_injective (WordToZ 8)).
 rewrite !rescale_field_output_value;reflexivity.
Qed.

Lemma mixed_xy_ratio_h_negative x z u (ax az bx:Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds z -> square_input_bounds u ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP=
 (-@toZ (WordToZ 8) (mixed_literal_h ax az bx)) mod feP.
Proof.
 intros BX BZ BU HX HZ HU;destruct (mixed_xy_weak_residue x BX) as [RX TX].
 rewrite mixed_literal_h_numeric.
 change (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP=
  (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP) mod feP).
 rewrite Zminus_mod_idemp_r.
 replace (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az)) with
  (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az-@toZ (WordToZ 8) ax) by ring.
 exact (mixed_h_residue _ _ _ _ _ _ TX BZ BU (eq_trans RX HX) HZ HU).
Qed.

Lemma mixed_ratio_negative_output h (a:Ty.tySem (Word 8)) :
 radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP ->
 rescale_field_output h=@canonical_fe_normalize Alg.CoreFunSem
  (@literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
Proof.
 intro RH;assert (Value:rescale_field_output h=@literal_fe_multiply Alg.CoreFunSem
  (a,@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 { apply (toZ_injective (WordToZ 8)).
   rewrite rescale_field_output_value,literal_multiply_numeric,literal_curve_negate_numeric,
     literal_fe_one256_value,field_prime_matches_normalizer,RH.
   rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
   replace (@toZ (WordToZ 8) a*((feP-1) mod feP)) with (@toZ (WordToZ 8) a*(feP-1)) at 1.
   2:{ rewrite Z.mod_small by (unfold feP,feR;lia);reflexivity. }
   replace (@toZ (WordToZ 8) a*(feP-1)) with (-@toZ (WordToZ 8) a+@toZ (WordToZ 8) a*feP) by ring.
   rewrite Z.mod_add by (unfold feP,feR;lia);reflexivity. }
 rewrite Value;symmetry;apply canonical_fe_normalize_reduced;rewrite literal_multiply_numeric.
 pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) a*@toZ (WordToZ 8)
  (@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))) feP
  ltac:(unfold feP,feR;lia)) as Bound;lia.
Qed.

Theorem mixed_xy_ratio_outputs_literal x y z u v (ax ay az bx byword:Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 let flag:=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 rescale_field_output (mixed_mode_slice_ratio_words true flag x y z u v)=
 @canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))).
Proof.
 intros BX BY BZ BU BV HX HY HZ HU HV;cbv zeta.
 unfold mixed_mode_slice_ratio_words,bit_int;rewrite literal_gej_ge_add_ex_expansion.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:HInf.
 - change (rescale_field_output (point_set_bit_words false)=
    @canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_add_ex Alg.CoreFunSem
      (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt))))).
   assert (HA:@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt).
   { rewrite literal_gej_is_infinity_value.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unit|unit];destruct unit;[discriminate HInf|reflexivity]. }
   rewrite literal_gej_add_ex_fst_infinite by exact HA;rewrite canonical_fe_normalize_zero256;exact mixed_ratio_clear_output.
 - change (rescale_field_output (mixed_mode_finite_ratio_words true x y z u v)=
    @canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_add_ex Alg.CoreFunSem
      (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt))))).
   assert (HA:@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
   { rewrite literal_gej_is_infinity_value.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unit|unit];destruct unit;[reflexivity|discriminate HInf]. }
   unfold mixed_mode_finite_ratio_words.
   destruct (Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP) 0) eqn:HH.
   + assert (HZH:@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt).
     { rewrite (mixed_xy_h_test x z u ax az bx BX BZ BU HX HZ HU) in HH.
       destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [unit|unit];destruct unit;
        [discriminate HH|reflexivity]. }
     unfold mixed_zero_words;rewrite (mixed_xy_i_test y z v ay az byword BY BZ BV HY HZ HV).
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)) as [unit|unit] eqn:HI;
      destruct unit;cbn [Bit.toBool].
     * rewrite literal_gej_add_ex_fst_zero_h_nonzero_i by assumption;rewrite canonical_fe_normalize_zero256.
       exact zero_field_writer_literal_output.
     * rewrite literal_gej_add_ex_fst_equal_point by assumption;apply mixed_xy_output_normalize.
       exact (eq_trans (proj1 (mixed_xy_weak_residue y BY)) HY).
   + assert (HZH:@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inl tt).
     { rewrite (mixed_xy_h_test x z u ax az bx BX BZ BU HX HZ HU) in HH.
       destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [unit|unit];destruct unit;
        [reflexivity|discriminate HH]. }
     rewrite literal_gej_add_ex_fst_nonzero_h by assumption;apply mixed_ratio_negative_output.
     exact (mixed_xy_ratio_h_negative x z u ax az bx BX BZ BU HX HZ HU).
Qed.

Theorem mixed_xy_ex_outputs_literal x y z u v (ax ay az bx byword:Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 let flag:=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 (rescale_field_output (mixed_mode_slice_ratio_words true flag x y z u v),
  ((rescale_field_output (mixed_mode_body_x_words true flag x y z u v),
    rescale_field_output (mixed_mode_body_y_words true flag x y z u v)),
    rescale_field_output (mixed_mode_body_z_words true flag x y z u v)))=
 (@canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))),
  snd (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))).
Proof.
 intros BX BY BZ BU BV HX HY HZ HU HV flag;f_equal.
 - exact (mixed_xy_ratio_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV).
 - exact (mixed_xy_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV).
Qed.

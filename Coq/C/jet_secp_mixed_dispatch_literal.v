(** C H/I dispatch compared with the exact literal mixed-addition tests. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_curve_mul
 C.jet_secp_field_mul_small C.jet_secp_mixed_difference C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_finite_prefix C.jet_secp_double_coordinate_numeric
 C.jet_secp_square_spec_bridge C.jet_secp_field_weak_tight C.jet_secp_rescale_literal
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_curve_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_negate_literal_contract
 C.jet_secp_add_literal C.jet_secp_add_literal_step C.jet_secp_literal_gej_predicate
 C.jet_secp_literal_infinity C.jet_secp_double_literal C.jet_secp_double_literal_bridge
 C.jet_secp_double_all_calls C.jet_secp_mixed_finite_body C.jet_secp_mixed_zero_return.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words mixed_difference_words.

Lemma mixed_difference_residue a b : mul_small_input_bounds a -> mul_small_input_bounds b ->
 radix_value (mixed_difference_words a b) mod feP=(radix_value b-radix_value a) mod feP.
Proof.
 intros BA BB;rewrite (proj1 (mixed_difference_numeric a b BA BB)).
 replace (4*feP-radix_value a+radix_value b) with
   ((radix_value b-radix_value a)+4*feP) by ring.
 apply Z.mod_add;unfold feP,feR;lia.
Qed.

Lemma mixed_literal_one_finite :
 @canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)=inl tt.
Proof.
 pose proof (literal_curve_zero_numeric (@literal_fe_one256 Alg.CoreFunSem tt)) as H.
 rewrite literal_fe_one256_value,Z.mod_small in H by (unfold feP,feR;lia).
 destruct (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) as [u|u];
   destruct u;[reflexivity|discriminate].
Qed.

Definition mixed_literal_h (a c b : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem
  (@literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)),
   @literal_fe_multiply Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem b,@literal_fe_square Alg.CoreFunSem c)).
Definition mixed_literal_i (a c b : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem
  (@literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)),
   @literal_fe_multiply Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem b,@literal_fe_cube Alg.CoreFunSem c)).
Lemma mixed_literal_h_numeric a c b : @toZ (WordToZ 8) (mixed_literal_h a c b)=
 (@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP.
Proof.
 unfold mixed_literal_h;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,
  !literal_multiply_numeric,!literal_square_numeric,literal_curve_negate_numeric,literal_fe_one256_value.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) a*(1*1)+(feP-@toZ (WordToZ 8) b)*(@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) with
  ((@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)+
    (@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)*feP) by ring.
 apply Z.mod_add;unfold feP,feR;lia.
Qed.
Lemma mixed_literal_i_numeric a c b : @toZ (WordToZ 8) (mixed_literal_i a c b)=
 (@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP.
Proof.
 unfold mixed_literal_i;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,
  !literal_multiply_numeric,!literal_curve_cube_numeric,literal_curve_negate_numeric,literal_fe_one256_value.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) a*(1*1*1)+(feP-@toZ (WordToZ 8) b)*(@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) with
  ((@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)+
    (@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)*feP) by ring.
 apply Z.mod_add;unfold feP,feR;lia.
Qed.
Lemma mixed_residue_difference u v a b : u mod feP=a mod feP -> v mod feP=b mod feP ->
 (u-v) mod feP=(a-b) mod feP.
Proof. intros HU HV;rewrite (Zminus_mod u v feP),(Zminus_mod a b feP),HU,HV;reflexivity. Qed.

Lemma mixed_h_residue x z u a c b :
 mul_small_input_bounds x -> square_input_bounds z -> square_input_bounds u ->
 radix_value x mod feP=a mod feP -> radix_value z mod feP=c mod feP -> radix_value u mod feP=b mod feP ->
 radix_value (mixed_h_words x z u) mod feP=(b*c*c-a) mod feP.
Proof.
 intros BX BZ BU HX HZ HU;unfold mixed_h_words.
 pose proof (double_square_tight z BZ) as BS.
 pose proof (double_tight_loose _ BS) as BSL.
 rewrite mixed_difference_residue by (try assumption;apply double_mul_tight;assumption).
 apply mixed_residue_difference;[|exact HX].
 rewrite (proj1 (curve_mul_value_bounds u (square_words z)
   (field_operand_from_bounds u BU) (field_operand_from_bounds _ BSL))).
 replace (b*c*c) with (b*(c*c)) by ring.
 apply double_residue_product;[exact HU|].
 rewrite <-field_prime_matches_normalizer,(square_output_numeric z BZ),field_prime_matches_normalizer.
 apply double_residue_product;exact HZ.
Qed.
Lemma mixed_i_residue y z v a c b :
 mul_small_input_bounds y -> square_input_bounds z -> square_input_bounds v ->
 radix_value y mod feP=a mod feP -> radix_value z mod feP=c mod feP -> radix_value v mod feP=b mod feP ->
 radix_value (mixed_i_words y z v) mod feP=(a-b*c*c*c) mod feP.
Proof.
 intros BY BZ BV HY HZ HV;unfold mixed_i_words.
 pose proof (double_tight_loose _ (double_square_tight z BZ)) as BS.
 pose proof (double_tight_loose _ (double_mul_tight v (square_words z) BV BS)) as BP.
 rewrite mixed_difference_residue by (try assumption;apply double_mul_tight;assumption).
 apply mixed_residue_difference;[exact HY|].
 rewrite (proj1 (curve_mul_value_bounds (point_mul_words v (square_words z)) z
   (field_operand_from_bounds _ BP) (field_operand_from_bounds z BZ))).
 apply double_residue_product;[|exact HZ].
 rewrite (proj1 (curve_mul_value_bounds v (square_words z)
   (field_operand_from_bounds v BV) (field_operand_from_bounds _ BS))).
 replace (b*c*c) with (b*(c*c)) by ring.
 apply double_residue_product;[exact HV|].
 rewrite <-field_prime_matches_normalizer,(square_output_numeric z BZ),field_prime_matches_normalizer.
 apply double_residue_product;exact HZ.
Qed.

Lemma mixed_negated_zero_test a : Z.eqb ((-a) mod feP) 0=Z.eqb (a mod feP) 0.
Proof.
 apply Bool.eq_true_iff_eq;rewrite !Z.eqb_eq.
 rewrite !Z.mod_divide by (unfold feP,feR;lia).
 split;intros [q HQ];exists (-q);lia.
Qed.

Theorem mixed_h_reader_test (a c b : Ty.tySem (Word 8)) :
 Z.eqb (radix_value (mixed_h_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b)) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h a c b)).
Proof.
 assert (HR : radix_value (mixed_h_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b)) mod feP=
   (@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c-@toZ (WordToZ 8) a) mod feP).
 { apply mixed_h_residue;try apply square_reader_bounds;
     try (apply mixed_positioned_tight;apply square_reader_positioned);
     rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 rewrite HR,literal_curve_zero_numeric,mixed_literal_h_numeric,Z.mod_mod by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c-@toZ (WordToZ 8) a) with
  (-(@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) by ring.
 apply mixed_negated_zero_test.
Qed.
Theorem mixed_i_reader_test (a c b : Ty.tySem (Word 8)) :
 Z.eqb (radix_value (mixed_i_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b)) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i a c b)).
Proof.
 assert (HR : radix_value (mixed_i_words (square_reader_rho a) (square_reader_rho c) (square_reader_rho b)) mod feP=
   (@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP).
 { apply mixed_i_residue;try apply square_reader_bounds;
     try (apply mixed_positioned_tight;apply square_reader_positioned);
     rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 rewrite HR,literal_curve_zero_numeric,mixed_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.

Local Opaque literal_gej_ge_add rescale_field_output canonical_fe_is_zero.
Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int literal_fe_one256 literal_fe_zero256
 literal_gej_double literal_gej_infinity literal_gej_is_infinity.
Theorem mixed_finite_zero_reader_outputs_literal (ax ay az bx byword : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 Z.eqb (radix_value (mixed_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx)) mod feP) 0=Datatypes.true ->
 ((rescale_field_output (mixed_finite_x_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)),
   rescale_field_output (mixed_finite_y_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword))),
   rescale_field_output (mixed_finite_z_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros HFin HH.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [u|u];destruct u;[reflexivity|discriminate HFin]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
   by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt).
 { rewrite mixed_h_reader_test in HH.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [u|u];destruct u;
     [discriminate HH|reflexivity]. }
 unfold mixed_finite_x_words,mixed_finite_y_words,mixed_finite_z_words;rewrite HH.
 unfold mixed_zero_words;rewrite mixed_i_reader_test.
 rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta;fold (mixed_literal_h ax az bx) (mixed_literal_i ay az byword);rewrite HZH.
 destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)) as [u|u] eqn:HI;destruct u;
   cbn [Bit.toBool].
 - change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
     rescale_field_output (fun _ : nat=>Int64.zero))=
     ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
   assert (HZ : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
     by exact zero_field_writer_literal_output.
   rewrite HZ;reflexivity.
 - rewrite literal_gej_double_step,literal_gej_is_infinity_value,HFin.
   apply double_body_writer_outputs_literal;try apply square_reader_bounds;
     rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

(** Actual finite zinv coordinate words against the literal primitive-bearing program. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_weak_loose C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_dispatch_literal C.jet_secp_curve_literal C.jet_secp_canonical_zero
 C.jet_secp_mixed_nonzero_literal C.jet_secp_zinv_differences C.jet_secp_zinv_one_numeric
 C.jet_secp_zinv_literal C.jet_secp_zinv_finite C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail
 C.jet_secp_rescale_literal C.jet_secp_double_literal_bridge C.jet_secp_double_literal
 C.jet_secp_literal_gej_predicate C.jet_secp_add_literal C.jet_secp_add_literal_step
 C.jet_secp_literal_infinity C.jet_secp_double_all_calls C.jet_secp_multiply_literal_spec
 C.jet_secp_square_execution C.jet_secp_literal_add_program C.jet_secp_multiply_normalize_bridge
 C.jet_secp_negate_literal_contract C.jet_secp_literal_add_numeric C.jet_secp_square_numeric
 C.jet_secp_square_execution C.jet_secp_point_mul_numeric C.jet_secp_curve_mul C.jet_secp_field_mul_small
 C.jet_secp_zinv_infinite_products C.jet_secp_point_set_bit C.jet_secp_canonical_normalize
 C.jet_secp_mixed_infinite_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words square_words weak_loose_words rescale_field_output literal_gej_ge_add
 literal_gej_is_infinity canonical_fe_is_zero literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_add literal_fe_negate literal_fe_multiply_int literal_fe_one256 literal_fe_zero256
 literal_gej_double literal_gej_infinity.

Theorem zinv_finite_outputs_literal x y z u v inv (ax ay az bx byword : Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv -> radix_value inv mod feP=1 ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 ((rescale_field_output (zinv_finite_x x y z u v inv),rescale_field_output (zinv_finite_y x y z u v inv)),
   rescale_field_output (zinv_finite_z x y z u v inv))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros BX BY BZ BU BV BI One HX HY HZ HU HV HFin.
 assert (BX60 : forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60)
   by (intros j HJ;pose proof (square_input56 x BX j HJ);lia).
 assert (BY60 : forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60)
   by (intros j HJ;pose proof (square_input56 y BY j HJ);lia).
 destruct (zinv_differences_literal x y z u v inv ax ay az bx byword BX60 BY60 BZ BU BV BI One HX HY HZ HU HV)
   as (RH & RI & BH & BII).
 destruct (zinv_tests_literal x y z u v inv ax ay az bx byword BX60 BY60 BZ BU BV BI One HX HY HZ HU HV)
   as (TestH & TestI).
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unitA|unitA];destruct unitA;[reflexivity|discriminate HFin]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
   by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 unfold zinv_finite_x,zinv_finite_y,zinv_finite_z.
 rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta;fold (mixed_literal_h ax az bx) (mixed_literal_i ay az byword).
 destruct (Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0) eqn:HH.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt).
   { destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [unitH|unitH];
       destruct unitH;[discriminate TestH|reflexivity]. }
   rewrite HZH;unfold mixed_zero_words;rewrite TestI.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)) as [unitI|unitI] eqn:II;
     destruct unitI;cbn [Bit.toBool].
   + change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
       rescale_field_output (fun _ : nat=>Int64.zero))=
       ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
     assert (ZeroOut : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
       by exact zero_field_writer_literal_output.
     rewrite ZeroOut;reflexivity.
   + rewrite literal_gej_double_step,literal_gej_is_infinity_value,HFin.
     apply double_body_writer_outputs_literal;assumption.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inl tt).
   { destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [unitH|unitH];
       destruct unitH;[reflexivity|discriminate TestH]. }
   rewrite HZH.
   set (h := zinv_h_words x z u inv);set (i := zinv_i_words y z v inv).
   set (a := mixed_literal_h ax az bx);set (b := mixed_literal_i ay az byword).
   set (c := @literal_fe_multiply Alg.CoreFunSem (ax,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
   set (d := @literal_fe_multiply Alg.CoreFunSem (ay,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
   change (((rescale_field_output (mixed_nonzero_x_words h i (weak_loose_words x)),
     rescale_field_output (mixed_nonzero_y_words h i (weak_loose_words x) (weak_loose_words y))),
     rescale_field_output (point_mul_words z h))=((mixed_literal_rx a b c,mixed_literal_ry a b c d),mixed_literal_rz a az)).
   destruct (weak_loose_numeric x BX60) as [WX BWX];destruct (weak_loose_numeric y BY60) as [WY BWY].
   assert (RC : radix_value (weak_loose_words x) mod feP=@toZ (WordToZ 8) c mod feP).
   { unfold c;rewrite literal_multiply_numeric,literal_square_numeric,literal_fe_one256_value.
     rewrite Z.mod_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
     change (radix_value (weak_loose_words x) mod feP=(@toZ (WordToZ 8) ax*1) mod feP).
     rewrite Z.mul_1_r,WX;exact HX. }
   assert (RD : radix_value (weak_loose_words y) mod feP=@toZ (WordToZ 8) d mod feP).
   { unfold d;rewrite literal_multiply_numeric,literal_curve_cube_numeric,literal_fe_one256_value.
     rewrite Z.mod_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
     change (radix_value (weak_loose_words y) mod feP=(@toZ (WordToZ 8) ay*1) mod feP).
     rewrite Z.mul_1_r,WY;exact HY. }
   f_equal.
   + f_equal;apply double_field_output_matches.
     * exact (mixed_x_matches_literal h i (weak_loose_words x) a b c BH BII (double_tight_loose _ BWX) RH RI RC).
     * exact (mixed_y_matches_literal h i (weak_loose_words x) (weak_loose_words y) a b c d
         BH BII (double_tight_loose _ BWX) (double_tight_loose _ BWY) RH RI RC RD).
   + apply double_field_output_matches;exact (mixed_z_matches_literal z h a az BZ BH RH HZ).
Qed.

Theorem zinv_infinite_outputs_literal u v inv (ax ay az bx byword : Ty.tySem (Word 8)) :
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv -> radix_value inv mod feP=1 ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.true ->
 ((rescale_field_output (point_mul_words u (square_words inv)),
   rescale_field_output (point_mul_words v (zinv_inverse_cube inv))),
   rescale_field_output (point_set_bit_words true))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros BU BV BI One HU HV HInf.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unitA|unitA];destruct unitA;[discriminate HInf|reflexivity]. }
 assert (OneMod : 1 mod feP=1) by (apply Z.mod_small;unfold feP,feR;lia).
 assert (BS : square_input_bounds (square_words inv)) by (apply double_tight_loose;apply double_square_tight;exact BI).
 assert (SquareOne : radix_value (square_words inv) mod feP=1).
 { rewrite <-field_prime_matches_normalizer,(square_output_numeric inv BI),field_prime_matches_normalizer.
   rewrite (Z.mul_mod (radix_value inv) (radix_value inv) feP),One by (unfold feP,feR;lia).
   change (1 mod feP=1);exact OneMod. }
 assert (BC : square_input_bounds (zinv_inverse_cube inv)) by
   (apply double_tight_loose;apply double_mul_tight;assumption).
 assert (CubeOne : radix_value (zinv_inverse_cube inv) mod feP=1).
 { unfold zinv_inverse_cube;rewrite (proj1 (curve_mul_value_bounds (square_words inv) inv
     (field_operand_from_bounds _ BS) (field_operand_from_bounds _ BI))).
   rewrite (Z.mul_mod (radix_value (square_words inv)) (radix_value inv) feP),SquareOne,One by (unfold feP,feR;lia).
   change (1 mod feP=1);exact OneMod. }
 rewrite literal_gej_ge_add_infinite by exact HA.
 apply f_equal2;[apply f_equal2|exact mixed_one_output].
 all: apply double_field_output_matches.
 - rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
   rewrite (proj1 (curve_mul_value_bounds u (square_words inv) (field_operand_from_bounds _ BU) (field_operand_from_bounds _ BS))).
   rewrite (Z.mul_mod (radix_value u) (radix_value (square_words inv)) feP),SquareOne,
     Z.mul_1_r,Z.mod_mod by (unfold feP,feR;lia);exact HU.
 - rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
   rewrite (proj1 (curve_mul_value_bounds v (zinv_inverse_cube inv) (field_operand_from_bounds _ BV) (field_operand_from_bounds _ BC))).
   rewrite (Z.mul_mod (radix_value v) (radix_value (zinv_inverse_cube inv)) feP),CubeOne,
     Z.mul_1_r,Z.mod_mod by (unfold feP,feR;lia);exact HV.
Qed.

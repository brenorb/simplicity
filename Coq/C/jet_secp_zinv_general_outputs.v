(** Arbitrary-Z finite zinv coordinate words against the literal primitive-bearing program. *)
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
Require Import C.jet_toZ C.jet_secp_zinv_general_literal C.jet_secp_ge_zinv_literal C.jet_secp_ge_zinv_arithmetic.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words square_words weak_loose_words rescale_field_output literal_gej_ge_add
 literal_gej_is_infinity canonical_fe_is_zero literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_add literal_fe_negate literal_fe_multiply_int literal_fe_one256 literal_fe_zero256
 literal_gej_double literal_gej_infinity.

Theorem zinv_finite_outputs_scaled_literal x y z u v inv (ax ay az bx byword s : Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv -> radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 ((rescale_field_output (zinv_finite_x x y z u v inv),rescale_field_output (zinv_finite_y x y z u v inv)),
   rescale_field_output (zinv_finite_z x y z u v inv))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)).
Proof.
 intros BX BY BZ BU BV BI Scale HX HY HZ HU HV HFin.
 assert (BX60 : forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60)
   by (intros j HJ;pose proof (square_input56 x BX j HJ);lia).
 assert (BY60 : forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60)
   by (intros j HJ;pose proof (square_input56 y BY j HJ);lia).
 destruct (zinv_differences_scaled_literal x y z u v inv ax ay az bx byword s BX60 BY60 BZ BU BV BI Scale HX HY HZ HU HV)
   as (RH & RI & BH & BII).
 destruct (zinv_tests_scaled_literal x y z u v inv ax ay az bx byword s BX60 BY60 BZ BU BV BI Scale HX HY HZ HU HV)
   as (TestH & TestI).
 pose (sx:=fst (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))).
 pose (sy:=snd (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))).
 fold sx sy in RH,RI,TestH,TestI.
 assert (Scaled:@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)=(sx,sy)).
 { unfold sx,sy;destruct (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s));reflexivity. }
 rewrite Scaled.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unitA|unitA];destruct unitA;[reflexivity|discriminate HFin]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((sx,sy),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
   by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 unfold zinv_finite_x,zinv_finite_y,zinv_finite_z.
 rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta;fold (mixed_literal_h ax az sx) (mixed_literal_i ay az sy).
 destruct (Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0) eqn:HH.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az sx)=inr tt).
   { destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az sx)) as [unitH|unitH];
       destruct unitH;[discriminate TestH|reflexivity]. }
   rewrite HZH;unfold mixed_zero_words;rewrite TestI.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az sy)) as [unitI|unitI] eqn:II;
     destruct unitI;cbn [Bit.toBool].
   + change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
       rescale_field_output (fun _ : nat=>Int64.zero))=
       ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
     assert (ZeroOut : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
       by exact zero_field_writer_literal_output.
     rewrite ZeroOut;reflexivity.
   + rewrite literal_gej_double_step,literal_gej_is_infinity_value,HFin.
     apply double_body_writer_outputs_literal;assumption.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az sx)=inl tt).
   { destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az sx)) as [unitH|unitH];
       destruct unitH;[reflexivity|discriminate TestH]. }
   rewrite HZH.
   set (h := zinv_h_words x z u inv);set (i := zinv_i_words y z v inv).
   set (a := mixed_literal_h ax az sx);set (b := mixed_literal_i ay az sy).
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

Lemma zinv_normalize_writer_output w :
 @canonical_fe_normalize Alg.CoreFunSem (rescale_field_output w)=rescale_field_output w.
Proof.
 apply (toZ_injective (WordToZ 8)).
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model,
  rescale_field_output_value,field_prime_matches_normalizer.
 apply Z.mod_mod;unfold feP,feR;lia.
Qed.

Theorem zinv_infinite_outputs_scaled_literal u v inv (ax ay az bx byword s : Ty.tySem (Word 8)) :
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.true ->
 ((rescale_field_output (point_mul_words u (square_words inv)),
   rescale_field_output (point_mul_words v (zinv_inverse_cube inv))),
   rescale_field_output (point_set_bit_words true))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)).
Proof.
 intros BU BV BI Scale HU HV HInf.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unitA|unitA];destruct unitA;[discriminate HInf|reflexivity]. }
 pose proof (ge_zinv_words_literal u v inv bx byword s BU BV BI
  ltac:(rewrite field_prime_matches_normalizer;exact HU)
  ltac:(rewrite field_prime_matches_normalizer;exact HV)
  ltac:(rewrite field_prime_matches_normalizer;exact Scale)) as Scaled.
 rewrite <-Scaled.
 rewrite literal_gej_ge_add_infinite by exact HA.
 change (((rescale_field_output (point_mul_words u (square_words inv)),
   rescale_field_output (point_mul_words v (zinv_inverse_cube inv))),
   rescale_field_output (point_set_bit_words true))=
  ((@canonical_fe_normalize Alg.CoreFunSem (rescale_field_output (point_mul_words u (square_words inv))),
    @canonical_fe_normalize Alg.CoreFunSem (rescale_field_output (point_mul_words v (zinv_inverse_cube inv)))),
   @canonical_fe_normalize Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 rewrite !zinv_normalize_writer_output.
 f_equal;exact mixed_one_output.
Qed.

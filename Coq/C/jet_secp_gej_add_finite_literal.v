(** Finite projective machine outputs, including both H/I dispatches, decoded
    by the original writer against the complete fixed literal addition tree. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge C.jet_secp_point_mul_storage
 C.jet_secp_point_mul_numeric C.jet_secp_curve_mul C.jet_secp_field_mul_small C.jet_secp_double_coordinate_numeric
 C.jet_secp_gej_add_finite_difference C.jet_secp_gej_add_finite_body C.jet_secp_gej_add_dispatch_literal
 C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail C.jet_secp_mixed_dispatch_literal
 C.jet_secp_mixed_nonzero_literal C.jet_secp_double_all_calls C.jet_secp_double_literal_bridge
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_canonical_normalize
 C.jet_secp_add_literal C.jet_secp_add_literal_step C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity
 C.jet_secp_square_execution C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program
 C.jet_secp_literal_add_numeric C.jet_secp_negate_literal_contract C.jet_secp_curve_literal C.jet_secp_double_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words rescale_field_output literal_gej_add literal_gej_is_infinity
 canonical_fe_is_zero literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity.

Definition gej_add_literal_rz (a c d : Ty.tySem (Word 8)) :=
 @literal_fe_multiply Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (a,c),@literal_fe_negate Alg.CoreFunSem d).
Lemma gej_add_z_matches_literal z h w (a c d : Ty.tySem (Word 8)) :
 square_input_bounds z -> square_input_bounds h -> square_input_bounds w ->
 radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) c mod feP -> radix_value w mod feP=@toZ (WordToZ 8) d mod feP ->
 radix_value (point_mul_words z (point_mul_words h w)) mod feP=@toZ (WordToZ 8) (gej_add_literal_rz a c d).
Proof.
 intros BZ BH BW HH HZ HW.
 unfold gej_add_literal_rz;rewrite !literal_multiply_numeric,literal_curve_negate_numeric.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) a*@toZ (WordToZ 8) c*(feP-@toZ (WordToZ 8) d)) with
  ((@toZ (WordToZ 8) c*((-@toZ (WordToZ 8) a)*@toZ (WordToZ 8) d))+
    (@toZ (WordToZ 8) a*@toZ (WordToZ 8) c)*feP) by ring.
 rewrite Z.mod_add by (unfold feP,feR;lia).
 rewrite (proj1 (curve_mul_value_bounds z (point_mul_words h w) (field_operand_from_bounds z BZ)
   (field_operand_from_bounds _ (double_tight_loose _ (double_mul_tight h w BH BW))))).
 apply double_residue_product;[exact HZ|].
 rewrite (proj1 (curve_mul_value_bounds h w (field_operand_from_bounds h BH) (field_operand_from_bounds w BW))).
 apply double_residue_product;assumption.
Qed.
Lemma gej_add_literal_expansion (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))=
 snd (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))).
Proof. reflexivity. Qed.

Theorem gej_add_finite_reader_outputs_literal (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)=Datatypes.false ->
 ((rescale_field_output (gej_add_finite_x_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz)),
   rescale_field_output (gej_add_finite_y_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz))),
   rescale_field_output (gej_add_finite_z_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz)))=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)).
Proof.
 intros FinA FinB.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[reflexivity|discriminate FinA]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),bz)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem bz) as [[] | []];[reflexivity|discriminate FinB]. }
 rewrite gej_add_literal_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta.
 fold (gej_add_literal_u ax bz) (gej_add_literal_u (@literal_fe_negate Alg.CoreFunSem bx) az)
   (gej_add_literal_s ay bz) (gej_add_literal_s (@literal_fe_negate Alg.CoreFunSem byword) az).
 fold (gej_add_literal_h ax az bx bz) (gej_add_literal_i ay az byword bz).
 unfold gej_add_finite_x_words,gej_add_finite_y_words,gej_add_finite_z_words.
 destruct (Z.eqb (radix_value (gej_add_h_words (square_reader_rho ax) (square_reader_rho az)
   (square_reader_rho bx) (square_reader_rho bz)) mod feP) 0) eqn:HH.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)=inr tt).
   { rewrite gej_add_h_reader_test in HH.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)) as [[] | []];
       [discriminate HH|reflexivity]. }
   rewrite HZH;unfold mixed_zero_words;rewrite gej_add_i_reader_test.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_i ay az byword bz)) as [[] | []] eqn:HI;
     cbn [Bit.toBool].
   + change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
       rescale_field_output (fun _ : nat=>Int64.zero))=
       ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
     assert (Zero : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
       by exact zero_field_writer_literal_output.
     rewrite Zero;reflexivity.
   + rewrite literal_gej_double_step,literal_gej_is_infinity_value,FinA.
     apply double_body_writer_outputs_literal;try apply square_reader_bounds;
       rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)=inl tt).
   { rewrite gej_add_h_reader_test in HH.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)) as [[] | []];
       [reflexivity|discriminate HH]. }
   rewrite HZH.
   set (h := gej_add_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx) (square_reader_rho bz)).
   set (i := gej_add_i_words (square_reader_rho ay) (square_reader_rho az) (square_reader_rho byword) (square_reader_rho bz)).
   set (u := gej_add_u1_words (square_reader_rho ax) (square_reader_rho bz)).
   set (s := gej_add_s1_words (square_reader_rho ay) (square_reader_rho bz)).
   set (a := gej_add_literal_h ax az bx bz);set (b := gej_add_literal_i ay az byword bz).
   set (c := gej_add_literal_u ax bz);set (d := gej_add_literal_s ay bz).
   change (((rescale_field_output (mixed_nonzero_x_words h i u),rescale_field_output (mixed_nonzero_y_words h i u s)),
     rescale_field_output (point_mul_words (square_reader_rho az) (point_mul_words h (square_reader_rho bz))))=
     ((mixed_literal_rx a b c,mixed_literal_ry a b c d),gej_add_literal_rz a az bz)).
   assert (BH : square_input_bounds h) by (unfold h;apply gej_add_h_bounds;apply square_reader_bounds).
   assert (BI : square_input_bounds i) by (unfold i;apply gej_add_i_bounds;apply square_reader_bounds).
   assert (BU : square_input_bounds u).
   { unfold u,gej_add_u1_words;apply double_tight_loose;apply double_mul_tight;[apply square_reader_bounds|].
     apply double_tight_loose;apply double_square_tight;apply square_reader_bounds. }
   assert (BS : square_input_bounds s).
   { unfold s,gej_add_s1_words;apply double_tight_loose;apply double_mul_tight;[|apply square_reader_bounds].
     apply double_tight_loose;apply double_mul_tight;[apply square_reader_bounds|].
     apply double_tight_loose;apply double_square_tight;apply square_reader_bounds. }
   assert (RH : radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP) by (exact (gej_add_h_reader_residue ax az bx bz)).
   assert (RI : radix_value i mod feP=@toZ (WordToZ 8) b mod feP) by (exact (gej_add_i_reader_residue ay az byword bz)).
   assert (RU : radix_value u mod feP=@toZ (WordToZ 8) c mod feP) by (exact (gej_add_u_reader_residue ax bz)).
   assert (RS : radix_value s mod feP=@toZ (WordToZ 8) d mod feP) by (exact (gej_add_s_reader_residue ay bz)).
   f_equal.
   + f_equal;apply double_field_output_matches.
     * apply mixed_x_matches_literal;assumption.
     * apply mixed_y_matches_literal;assumption.
   + apply double_field_output_matches;apply gej_add_z_matches_literal;try apply square_reader_bounds;try assumption;
       rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

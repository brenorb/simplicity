(** The actual finite helper's stored infinity flag is consistent with its
    actual Z output. This is needed by C callers which inspect the flag rather
    than serialize the coordinates; it is not a substitute for execution. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_point_mul_numeric C.jet_secp_curve_mul C.jet_secp_square_columns
 C.jet_secp_double_coordinate_numeric C.jet_secp_double_var_owned C.jet_secp_double_all_calls
 C.jet_secp_mixed_zero_return C.jet_secp_gej_add_finite_difference C.jet_secp_gej_add_finite_body
 C.jet_secp_field_prime C.jet_secp_gej_add_dispatch_literal C.jet_secp_gej_add_finite_literal C.jet_secp_gej_add_finite_generic
 C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal C.jet_secp_canonical_normalize
 C.jet_secp_canonical_zero C.jet_secp_curve_literal C.jet_secp_literal_gej_predicate C.jet_secp_add_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words square_reader_rho rescale_field_output literal_gej_add literal_gej_is_infinity canonical_fe_is_zero.

Lemma gej_add_finite_flag_consistent x y z u v w :
 square_input_bounds z -> square_input_bounds w -> square_input_bounds (gej_add_h_words x z u w) ->
 radix_value z mod feP<>0 -> radix_value w mod feP<>0 ->
 Int.eq (gej_add_finite_flag x y z u v w) Int.one=
 Z.eqb (radix_value (gej_add_finite_z_words x y z u v w) mod feP) 0.
Proof.
 intros BZ BW BH NZ NW.
 unfold gej_add_finite_flag,gej_add_finite_z_words.
 destruct (Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0) eqn:HH.
 - unfold mixed_zero_flag,mixed_zero_words.
   destruct (Z.eqb (radix_value (gej_add_i_words y z v w) mod feP) 0).
   + unfold double_var_zflag;destruct (Z.eqb (radix_value (double_output_z_words y z) mod feP) 0);reflexivity.
   + reflexivity.
 - apply Z.eqb_neq in HH.
   assert (NT : radix_value (point_mul_words (gej_add_h_words x z u w) w) mod feP<>0).
   { rewrite (proj1 (curve_mul_value_bounds (gej_add_h_words x z u w) w
       (field_operand_from_bounds _ BH) (field_operand_from_bounds w BW))).
     apply secp256k1_nonzero_product;assumption. }
   assert (NR : radix_value (point_mul_words z (point_mul_words (gej_add_h_words x z u w) w)) mod feP<>0).
   { rewrite (proj1 (curve_mul_value_bounds z (point_mul_words (gej_add_h_words x z u w) w)
       (field_operand_from_bounds z BZ) (field_operand_from_bounds _
         (double_tight_loose _ (double_mul_tight _ w BH BW))))).
     apply secp256k1_nonzero_product;assumption. }
   symmetry;apply Z.eqb_neq;exact NR.
Qed.

Lemma gej_add_finite_flag_bit x y z u v w :
 gej_add_finite_flag x y z u v w=bit_int (Int.eq (gej_add_finite_flag x y z u v w) Int.one).
Proof.
 unfold gej_add_finite_flag,mixed_zero_flag,double_var_zflag.
 destruct (Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0);
   destruct (Z.eqb (radix_value (gej_add_i_words y z v w) mod feP) 0);
   destruct (Z.eqb (radix_value (double_output_z_words y z) mod feP) 0);reflexivity.
Qed.

Theorem gej_add_finite_flag_matches_literal mx my mz mu mv mw (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 square_input_bounds mx -> square_input_bounds my -> square_input_bounds mz ->
 square_input_bounds mu -> square_input_bounds mv -> square_input_bounds mw ->
 radix_value mx mod feP=@toZ (WordToZ 8) ax mod feP -> radix_value my mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value mz mod feP=@toZ (WordToZ 8) az mod feP -> radix_value mu mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value mv mod feP=@toZ (WordToZ 8) byword mod feP -> radix_value mw mod feP=@toZ (WordToZ 8) bz mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)=false ->
 Int.eq (gej_add_finite_flag mx my mz mu mv mw) Int.one=
 Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
   (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))).
Proof.
 intros BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FinA FinB.
 pose proof (gej_add_finite_outputs_literal mx my mz mu mv mw ax ay az bx byword bz
   BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FinA FinB) as Literal.
 pose proof (f_equal (fun p : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) =>
   Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem p)) Literal) as Flag.
 rewrite gej_add_finite_flag_consistent.
 - rewrite <-Flag,literal_gej_is_infinity_value,literal_curve_zero_numeric,
     rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
 - exact BMZ.
 - exact BMW.
 - apply gej_add_h_bounds;assumption.
 - rewrite RMZ;rewrite literal_curve_zero_numeric in FinA;apply Z.eqb_neq;exact FinA.
 - rewrite RMW;rewrite literal_curve_zero_numeric in FinB;apply Z.eqb_neq;exact FinB.
Qed.

Theorem gej_add_finite_reader_flag_matches_literal (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)=false ->
 Int.eq (gej_add_finite_flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
   (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz)) Int.one=
 Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
   (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))).
Proof.
 intros FinA FinB.
 pose proof (gej_add_finite_reader_outputs_literal ax ay az bx byword bz FinA FinB) as Literal.
 pose proof (f_equal (fun p : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) =>
   Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem p)) Literal) as Flag.
 rewrite gej_add_finite_flag_consistent.
 - rewrite <-Flag,literal_gej_is_infinity_value,literal_curve_zero_numeric,
     rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia).
   reflexivity.
 - apply square_reader_bounds.
 - apply square_reader_bounds.
 - apply gej_add_h_bounds;apply square_reader_bounds.
 - rewrite <-field_prime_matches_normalizer,rescale_reader_residue.
   rewrite literal_curve_zero_numeric in FinA;apply Z.eqb_neq;exact FinA.
 - rewrite <-field_prime_matches_normalizer,rescale_reader_residue.
   rewrite literal_curve_zero_numeric in FinB;apply Z.eqb_neq;exact FinB.
Qed.

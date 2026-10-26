(** The mixed-addition C infinity flag remains the zero test of its actual
    Z field. This representation invariant lets the next table iteration
    use the literal-program bridge; it is proved, not assumed at each step. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_secp_fe_math C.jet_secp_field_prime
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_field_zero_owned C.jet_secp_point_mul_numeric C.jet_secp_point_mul_storage
 C.jet_secp_mixed_body_loose C.jet_secp_mixed_xy_literal C.jet_secp_mixed_preparation_loose
 C.jet_secp_mixed_finite_return C.jet_secp_mixed_difference C.jet_secp_mixed_zero_return
 C.jet_secp_double_var_owned C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric
 C.jet_secp_field_mul_small C.jet_secp_point_set_bit C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words.

Lemma mixed_flag_of_residue z (az:Ty.tySem (Word 8)) :
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 field_zero_result z=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)).
Proof.
 intro Residue;unfold field_zero_result,bit_int.
 rewrite <-canonical_fe_zero_after_normalize,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
 rewrite Residue;reflexivity.
Qed.

Theorem mixed_xy_flag_preserved x y z u v flag :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> flag=field_zero_result z ->
 mixed_mode_body_flag true flag x y z u v=
 field_zero_result (mixed_mode_body_z_words true flag x y z u v).
Proof.
 intros BX BY BZ BU BV Flag;subst flag.
 unfold mixed_mode_body_flag,mixed_mode_body_z_words,field_zero_result.
 destruct (Z.eqb (radix_value z mod feP) 0) eqn:HZ.
 - change (Int.zero=if Z.eqb (radix_value (point_set_bit_words true) mod feP) 0 then Int.one else Int.zero).
   reflexivity.
 - change (mixed_mode_finite_flag true x y z u v=
    if Z.eqb (radix_value (mixed_mode_finite_z_words true x y z u v) mod feP) 0 then Int.one else Int.zero).
   unfold mixed_mode_finite_flag,mixed_mode_finite_z_words.
   destruct (Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP) 0) eqn:HH.
   + unfold mixed_zero_flag,mixed_zero_words.
     destruct (Z.eqb (radix_value (mixed_i_words (C.jet_secp_field_weak_loose.weak_loose_words y) z v) mod feP) 0);
      unfold double_var_zflag;reflexivity.
   + set (h:=mixed_h_words (mixed_x_words true x) z u) in *.
     destruct (mixed_xy_weak_residue x BX) as [RX TX].
     assert (BH:square_input_bounds h).
     { unfold h,mixed_h_words;apply (proj2 (mixed_difference_numeric _ _ TX
        (double_mul_tight _ _ BU (double_tight_loose _ (double_square_tight _ BZ))))). }
     assert (Nonzero:radix_value (point_mul_words z h) mod feP<>0).
     { rewrite <-field_prime_matches_normalizer,(proj1 (point_mul_value_and_bounds z h BZ BH)),field_prime_matches_normalizer.
       apply secp256k1_nonzero_product;apply Z.eqb_neq;assumption. }
     rewrite (proj2 (Z.eqb_neq _ _) Nonzero);reflexivity.
Qed.

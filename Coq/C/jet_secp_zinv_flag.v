(** Stored C flag agrees with the actual zinv output Z. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import C.jet_readBit_layout C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_curve_mul
 C.jet_secp_square_columns C.jet_secp_double_var_owned C.jet_secp_double_all_calls
 C.jet_secp_double_coordinate_numeric C.jet_secp_mixed_zero_return C.jet_secp_zinv_differences
 C.jet_secp_zinv_finite C.jet_secp_field_prime.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words.

Theorem zinv_finite_flag_consistent x y z u v inv :
 square_input_bounds z -> square_input_bounds (zinv_h_words x z u inv) ->
 radix_value z mod feP<>0 ->
 zinv_finite_flag x y z u v inv =
 bit_int (Z.eqb (radix_value (zinv_finite_z x y z u v inv) mod feP) 0).
Proof.
 intros BZ BH NZ.
 unfold zinv_finite_flag,zinv_finite_z.
 destruct (Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0) eqn:HH.
 - unfold mixed_zero_flag,mixed_zero_words.
   destruct (Z.eqb (radix_value (zinv_i_words y z v inv) mod feP) 0).
   + unfold double_var_zflag,bit_int.
     destruct (Z.eqb (radix_value (double_output_z_words y z) mod feP) 0);reflexivity.
   + reflexivity.
 - apply Z.eqb_neq in HH.
   assert (NR : radix_value (point_mul_words z (zinv_h_words x z u inv)) mod feP<>0).
   { rewrite (proj1 (curve_mul_value_bounds z (zinv_h_words x z u inv)
       (field_operand_from_bounds z BZ) (field_operand_from_bounds _ BH))).
     apply secp256k1_nonzero_product;assumption. }
   apply Z.eqb_neq in NR;rewrite NR;reflexivity.
Qed.

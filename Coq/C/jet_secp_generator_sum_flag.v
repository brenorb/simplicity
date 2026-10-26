(** The actual mixed-addition infinity flag for the generator's Z=1 input.
    This permits both finite and infinite sums in the subsequent caller. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_field_mul_small C.jet_secp_curve_mul C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
  C.jet_secp_double_coordinate_numeric C.jet_secp_double_var_owned
  C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_body_loose C.jet_secp_mixed_finite_return
  C.jet_secp_mixed_zero_return C.jet_secp_mixed_difference C.jet_secp_point_set_bit
  C.jet_secp_mixed_infinite_literal C.jet_secp_mixed_xy_literal
  C.jet_secp_curve_literal C.jet_secp_canonical_zero C.jet_secp_rescale_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words square_words.

Lemma generator_one_radix : radix_value (point_set_bit_words true)=1.
Proof. vm_compute;reflexivity. Qed.

Theorem generator_sum_flag_consistent x y u v :
  square_input_bounds x ->square_input_bounds y ->square_input_bounds u ->square_input_bounds v ->
  mixed_mode_body_flag true Int.zero x y (point_set_bit_words true) u v=
    bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
      (rescale_field_output (mixed_mode_body_z_words true Int.zero x y (point_set_bit_words true) u v)))).
Proof.
  intros BX BY BU BV.
  rewrite literal_curve_zero_numeric,rescale_field_output_value,field_prime_matches_normalizer,
    Z.mod_mod by (unfold feP,feR;lia).
  unfold mixed_mode_body_flag,mixed_mode_body_z_words;rewrite Int.eq_true.
  unfold mixed_mode_finite_flag,mixed_mode_finite_z_words.
  destruct (Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) (point_set_bit_words true) u) mod feP) 0) eqn:TestH.
  - unfold mixed_zero_flag,mixed_zero_words.
    destruct (Z.eqb (radix_value (mixed_i_words (C.jet_secp_field_weak_loose.weak_loose_words y)
      (point_set_bit_words true) v) mod feP) 0).
    + unfold double_var_zflag,bit_int;reflexivity.
    + change (Int.one=bit_int true);reflexivity.
  - destruct (mixed_xy_weak_residue x BX) as [RX TX].
    assert (BH:square_input_bounds (mixed_h_words (mixed_x_words true x) (point_set_bit_words true) u)).
    { unfold mixed_h_words;apply (proj2 (mixed_difference_numeric _ _ TX
        (double_mul_tight _ _ BU (double_tight_loose _ (double_square_tight _ mixed_one_bounds))))). }
    rewrite (proj1 (curve_mul_value_bounds (point_set_bit_words true)
      (mixed_h_words (mixed_x_words true x) (point_set_bit_words true) u)
      (field_operand_from_bounds _ mixed_one_bounds) (field_operand_from_bounds _ BH))),
      generator_one_radix,Z.mul_1_l,TestH;reflexivity.
Qed.

(** Reader-derived residues connect the helper result to the guarded literal term. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal C.jet_secp_curve_literal_bridge.
Require Import C.jet_secp_x_equiv_function C.jet_secp_x_equiv_literal C.jet_secp_canonical_zero C.jet_secp_curve_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma x_equiv_reader_product_residue (q z : tySem (Word 8)) :
  (radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*
    radix_value (square_reader_rho q)) mod feP =
    (@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) q) mod feP.
Proof.
  rewrite Z.mul_mod by (unfold feP,feR;lia).
  rewrite curve_reader_square_residue.
  change (((@toZ (WordToZ 8) z*@toZ (WordToZ 8) z) mod field_prime *
    (radix_value (square_reader_rho q) mod field_prime)) mod field_prime =
    (@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) q) mod field_prime).
  rewrite rescale_reader_residue, <- Z.mul_mod by (unfold field_prime,field_c;lia);reflexivity.
Qed.

Lemma x_equiv_guarded_result_literal (q x y z : tySem (Word 8)) :
  (if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z) then Int.zero else
    x_equiv_result (square_reader_rho q) (square_reader_rho x) (square_reader_rho z)) =
  bit_int (Bit.toBool (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z)))).
Proof.
  unfold x_equiv_result,bit_int.
  rewrite literal_x_equiv_numeric, literal_curve_zero_numeric, x_equiv_reader_product_residue.
  assert (HX : radix_value (square_reader_rho x) mod feP = @toZ (WordToZ 8) x mod feP)
    by exact (rescale_reader_residue x).
  rewrite HX.
  destruct (Z.eqb (@toZ (WordToZ 8) z mod feP) 0);reflexivity.
Qed.
Print Assumptions x_equiv_guarded_result_literal.

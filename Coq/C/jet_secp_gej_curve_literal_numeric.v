(** Arithmetic bridge for the existing literal projective curve program.
    Used to relate the actual helper's final comparison to its fixed target. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_literal
  C.jet_secp_square_execution C.jet_secp_multiply_literal_spec
  C.jet_secp_negate_literal_contract C.jet_secp_canonical_zero
  C.jet_secp_literal_add_numeric C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma gej_curve_six_mod z :
  ((z*z*z) mod feP*((z*z*z) mod feP)) mod feP=(z*z*z*z*z*z) mod feP.
Proof.
  rewrite <- Z.mul_mod by (unfold feP,feR;lia);f_equal;ring.
Qed.

Theorem literal_gej_curve_numeric (x y z : Ty.tySem (Word 8)) :
  Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z)) =
  Z.eqb ((@toZ (WordToZ 8) y * @toZ (WordToZ 8) y) mod feP)
    ((@toZ (WordToZ 8) x * @toZ (WordToZ 8) x * @toZ (WordToZ 8) x +
      7*(@toZ (WordToZ 8) z * @toZ (WordToZ 8) z * @toZ (WordToZ 8) z *
         @toZ (WordToZ 8) z * @toZ (WordToZ 8) z * @toZ (WordToZ 8) z)) mod feP).
Proof.
  rewrite literal_gej_curve_step,literal_curve_zero_numeric.
  rewrite !literal_fe_add_numeric,canonical_field_order_matches_limb_model.
  rewrite literal_multiply_numeric,!literal_square_numeric,
    !literal_curve_cube_numeric,literal_curve_negate_numeric,literal_square_numeric,curve_seven_value.
  rewrite gej_curve_six_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
  repeat rewrite Z.mod_mod by (unfold feP,feR;lia).
  repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR;lia).
  repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR;lia).
  rewrite curve_mod_add_neg_eq.
  reflexivity.
Qed.

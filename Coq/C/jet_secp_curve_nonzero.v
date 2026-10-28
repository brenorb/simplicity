(** A valid affine input cannot have y=0 in the fixed secp256k1 field.
    This discharges the first doubled-Z denominator of the original table. *)
From Coq Require Import ZArith Zpow_facts Lia.
Require Import C.jet_secp_fe_math C.jet_secp_curve_polynomial.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma secp_minus_seven_not_cube :
 Zpow_mod (-7) (Z.pos secp_cubic_exponent) feP<>1.
Proof. vm_compute;discriminate. Qed.

Theorem secp_curve_y_nonzero x y :
 (x*x*x+7) mod feP=(y*y) mod feP -> y mod feP<>0.
Proof.
 intros Curve Zero.
 assert (Positive:0<feP) by (unfold feP,feR;lia).
 pose proof (secp_curve_x_nonzero x y Curve) as Xnonzero.
 pose proof (secp_cubic_character x Xnonzero) as Cube.
 assert (CurveZero:(x*x*x+7) mod feP=0).
 { rewrite Curve,Z.mul_mod,Zero,Z.mul_0_l,Z.mod_0_l by lia;reflexivity. }
 assert (MinusSeven:(x*x*x) mod feP=(-7) mod feP).
 { replace (x*x*x) with ((x*x*x+7)+(-7)) at 1 by ring.
   rewrite Z.add_mod,CurveZero,Z.add_0_l,Z.mod_mod by lia;reflexivity. }
 rewrite Zpower_mod,MinusSeven,<-Zpower_mod in Cube by exact Positive.
 rewrite <-Zpow_mod_correct in Cube by lia.
 exact (secp_minus_seven_not_cube Cube).
Qed.

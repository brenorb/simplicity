(** Normalize genuine Jacobian coordinates into the verified affine group. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_jacobian_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_affine_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Notation "x + y" := (GZnZ.add feP x y).
Local Notation "x * y" := (GZnZ.mul feP x y).
Local Notation "x - y" := (GZnZ.sub feP x y).
Local Notation "x / y" := (GZnZ.div feP x y).
Local Notation "- x" := (GZnZ.opp feP x).
Local Notation "0" := (GZnZ.zero feP).
Local Notation "1" := (GZnZ.one feP).
Lemma secp_jacobian_affine_curve x y z (Curve:secp_jacobian_curve x y z) (Nonzero:z<>0):
 SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (y/(z*z*z)) 2=
 GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (x/(z*z)) 3)
 (GZnZ.mul feP (GZnZ.zero feP) (x/(z*z)))) secp_group_seven.
Proof.
 cbn [SMain.pow];unfold secp_jacobian_curve,secp_group_field in *.
 field [Curve];exact Nonzero.
Qed.
Lemma secp_jacobian_affine_value x y z (Curve:secp_jacobian_curve x y z) (Nonzero:z<>0):
 secp_jacobian_group_value x y z Curve=
 SMain.curve_elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP) (GZnZ.zero feP) secp_group_seven
 (x/(z*z)) (y/(z*z*z)) (secp_jacobian_affine_curve x y z Curve Nonzero).
Proof.
 unfold secp_jacobian_group_value,secp_jacobian_projective,SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test (z*z*z))) as [b Test];destruct b.
 - exfalso;pose proof (proj1 (SMain.is_zero_correct secp_group_theory (z*z*z)) Test) as Zero.
   revert Zero;repeat apply (SMain.Kmult_integral_contrapositive secp_group_theory);exact Nonzero.
 - apply (SMain.curve_elt_irr secp_group_theory);[|reflexivity].
   field;exact Nonzero.
Qed.
Lemma secp_jacobian_group_value_ext (x1 y1 z1 x2 y2 z2:secp_group_field)
 (C1:secp_jacobian_curve x1 y1 z1) (C2:secp_jacobian_curve x2 y2 z2):
 x1=x2 ->y1=y2 ->z1=z2 ->
 secp_jacobian_group_value x1 y1 z1 C1=secp_jacobian_group_value x2 y2 z2 C2.
Proof.
 intros X Y Z;subst x2 y2 z2;unfold secp_jacobian_group_value.
 f_equal;apply secp_jacobian_projective_irrelevance.
Qed.

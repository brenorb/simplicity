(** Group interpretation of the exact halved-slope Jacobian doubling formulas.
    The separate word bridge must connect the literal program to these field
    expressions. Zero and finite coordinates are retained in this result. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_certificate.
Require Import C.jet_secp_jacobian_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_double_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Notation "x + y" := (GZnZ.add feP x y).
Local Notation "x * y" := (GZnZ.mul feP x y).
Local Notation "x - y" := (GZnZ.sub feP x y).
Local Notation "x / y" := (GZnZ.div feP x y).
Local Notation "- x" := (GZnZ.opp feP x).
Local Notation "0" := (GZnZ.zero feP).
Local Notation "1" := (GZnZ.one feP).
Definition secp_jdouble_slope (x:secp_group_field):=((1+1+1)*x*x)/(1+1).
Definition secp_jdouble_x (x y:secp_group_field):=
 (secp_jdouble_slope x)*(secp_jdouble_slope x)-(1+1)*(y*y*x).
Definition secp_jdouble_y (x y:secp_group_field):=
 -(secp_jdouble_slope x*(secp_jdouble_x x y-y*y*x)+(y*y)*(y*y)).
Lemma secp_jacobian_double_curve x y z (Curve:secp_jacobian_curve x y z):
 secp_jacobian_curve (secp_jdouble_x x y) (secp_jdouble_y x y) (y*z).
Proof.
 unfold secp_jacobian_curve in *;unfold secp_jdouble_y,secp_jdouble_x,secp_jdouble_slope.
 unfold secp_group_field in *.
 field [Curve];exact (SMain.two_not_zero secp_group_theory).
Qed.
Lemma secp_jacobian_double_group x y z (Curve:secp_jacobian_curve x y z):
 secp_jacobian_group_value (secp_jdouble_x x y) (secp_jdouble_y x y) (y*z)
  (secp_jacobian_double_curve x y z Curve)=
 SMain.add secp_group_theory (secp_jacobian_group_value x y z Curve)
  (secp_jacobian_group_value x y z Curve).
Proof.
 unfold secp_jacobian_group_value;rewrite <-SMain.pe2e_double.
 apply secp_projective_group_equal;
 unfold secp_jacobian_projective,SMain.pdouble;
 destruct (secp_group_zero_test (z*z*z)) eqn:Test;
 cbn [SMain.x SMain.y SMain.z SMain.pow].
 - pose proof (proj1 (SMain.is_zero_correct secp_group_theory (z*z*z)) Test) as Zero.
   assert (Zzero:z=0).
   { destruct (SMain.Kmult_integral secp_group_theory (z*z) z Zero) as [Pair|Single];[|exact Single].
     destruct (SMain.Kmult_integral secp_group_theory z z Pair);assumption. }
   rewrite Zzero;split;intro H;ring.
 - assert (Znonzero:z<>0).
   { intro E;assert (C:z*z*z=0) by (rewrite E;ring).
     pose proof (proj2 (SMain.is_zero_correct secp_group_theory (z*z*z)) C);congruence. }
   unfold secp_group_field in *.
   split;intro Zero;destruct (SMain.Kdec secp_group_theory y 0) as [Yzero|Ynonzero].
   + rewrite Yzero;ring.
   + exfalso;revert Zero;repeat apply (SMain.Kmult_integral_contrapositive secp_group_theory);assumption.
   + rewrite Yzero;ring.
   + exfalso;revert Zero;repeat apply (SMain.Kmult_integral_contrapositive secp_group_theory);
     try assumption;exact (SMain.two_not_zero secp_group_theory).
 - pose proof (proj1 (SMain.is_zero_correct secp_group_theory (z*z*z)) Test) as Zero.
   unfold secp_jdouble_x,secp_jdouble_y,secp_jdouble_slope,secp_group_field in *.
   field [Zero];exact (SMain.two_not_zero secp_group_theory).
 - unfold secp_jdouble_x,secp_jdouble_y,secp_jdouble_slope,secp_group_field in *.
   field;exact (SMain.two_not_zero secp_group_theory).
 - pose proof (proj1 (SMain.is_zero_correct secp_group_theory (z*z*z)) Test) as Zero.
   unfold secp_jdouble_x,secp_jdouble_y,secp_jdouble_slope,secp_group_field in *.
   field [Zero];exact (SMain.two_not_zero secp_group_theory).
 - unfold secp_jdouble_y,secp_jdouble_x,secp_jdouble_slope,secp_group_field in *.
   field;exact (SMain.two_not_zero secp_group_theory).
Qed.

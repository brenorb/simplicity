(** Checked ordinary-projective generator coordinates for the original lambda
    constant. The coordinate certificate avoids expanding affine inversions;
    a separate proved projection rule gives its group interpretation. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_certificate C.jet_secp_scalar_lambda_global.
Require Import C.jet_secp_curve_group_endomorphism.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_lambda_projective:=secp_group_projective_power secp_group_generator_projective
 (Z.to_pos canonical_lambda_value).
Set Default Timeout 60.
Lemma secp_group_lambda_coordinates:
 let p:=secp_lambda_projective in
 GZnZ.val feP (SMain.z p)<>0 /\
 GZnZ.val feP (SMain.x p)=GZnZ.val feP (GZnZ.mul feP
   (GZnZ.mul feP secp_group_beta secp_group_generator_x) (SMain.z p)) /\
 GZnZ.val feP (SMain.y p)=GZnZ.val feP (GZnZ.mul feP secp_group_generator_y (SMain.z p)).
Proof. vm_compute;repeat split;discriminate. Qed.
Set Default Timeout 10.

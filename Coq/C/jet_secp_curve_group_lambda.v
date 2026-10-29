(** The actual beta endomorphism equals multiplication by the original lambda
    for every curve point. Generator coordinates, cyclicity and the power laws
    are proved inputs; no endomorphism or group-order premise is assumed. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_certificate C.jet_secp_scalar_lambda_global.
Require Import C.jet_secp_curve_group_endomorphism C.jet_secp_curve_group_lambda_certificate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_group_action_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Lemma secp_group_field_val_injective (x y:secp_group_field):
 GZnZ.val feP x=GZnZ.val feP y ->x=y.
Proof. destruct x,y;apply GZnZ.zirr. Qed.
Lemma secp_group_projective_affine (point:secp_group_projective) (x y:secp_group_field)
 (Curve:SMain.pow (GZnZ.one feP) (GZnZ.mul feP) y 2=
  GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) x 3)
  (GZnZ.mul feP (GZnZ.zero feP) x)) secp_group_seven):
 GZnZ.val feP (SMain.z point)<>0 ->
 GZnZ.val feP (SMain.x point)=GZnZ.val feP (GZnZ.mul feP x (SMain.z point)) ->
 GZnZ.val feP (SMain.y point)=GZnZ.val feP (GZnZ.mul feP y (SMain.z point)) ->
 SMain.pe2e secp_group_theory point=
 SMain.curve_elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP) (GZnZ.zero feP) secp_group_seven x y Curve.
Proof.
 destruct point as [px py pz Pc];cbn [SMain.x SMain.y SMain.z];intros Nz X Y.
 assert (Xeq:px=GZnZ.mul feP x pz) by (apply secp_group_field_val_injective;exact X).
 assert (Yeq:py=GZnZ.mul feP y pz) by (apply secp_group_field_val_injective;exact Y).
 assert (Nonzero:pz<>GZnZ.zero feP).
 { intro Bad;apply Nz;rewrite Bad;reflexivity. }
 unfold SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test pz)) as [b Test];destruct b.
 - exfalso;apply Nz;unfold secp_group_zero_test in Test;apply Z.eqb_eq;exact Test.
 - apply (SMain.curve_elt_irr secp_group_theory).
   + rewrite Xeq;field;exact Nonzero.
   + rewrite Yeq;field;exact Nonzero.
Qed.
Lemma secp_group_lambda_generator:
 EGroup.gpow secp_group_generator secp_curve_group canonical_lambda_value=
 secp_group_endomorphism secp_group_generator.
Proof.
 pose proof secp_group_lambda_coordinates as [Nonzero [X Y]].
 assert (Projected:SMain.pe2e secp_group_theory secp_lambda_projective=
  secp_group_endomorphism secp_group_generator).
 { apply secp_group_projective_affine;assumption. }
 unfold secp_lambda_projective in Projected.
 rewrite secp_group_projective_power_correct,secp_group_generator_projective_value,
  secp_group_power_pos_correct in Projected.
 exact Projected.
Local Opaque EGroup.gpow secp_group_endomorphism secp_group_generator SMain.pe2e
 secp_group_projective_power secp_group_power_pos.
Qed.
Require Import C.jet_secp_curve_group_cyclic C.jet_secp_curve_group_odd C.jet_secp_canonical_scalar_lambda.
Local Transparent secp_group_endomorphism secp_group_power_pos.
Lemma secp_group_endo_infinity:secp_group_endomorphism secp_group_infinity=secp_group_infinity.
Proof. reflexivity. Qed.
Local Opaque secp_group_endomorphism.
Lemma secp_group_endo_positive_power point k:
 secp_group_endomorphism (secp_group_power_pos point k)=
 secp_group_power_pos (secp_group_endomorphism point) k.
Proof.
 induction k as [k IH|k IH|];cbn [secp_group_power_pos];unfold secp_group_add.
 - rewrite !secp_group_endo_add,IH;reflexivity.
 - rewrite secp_group_endo_add,IH;reflexivity.
 - reflexivity.
Qed.
Lemma secp_group_endo_power point k:0<=k ->
 secp_group_endomorphism (EGroup.gpow point secp_curve_group k)=
 EGroup.gpow (secp_group_endomorphism point) secp_curve_group k.
Proof.
 intro Nonnegative;destruct k as [|k|k].
 - change (secp_group_endomorphism secp_group_infinity=secp_group_infinity).
   exact secp_group_endo_infinity.
 - transitivity (secp_group_endomorphism (secp_group_power_pos point k)).
   + f_equal;symmetry;apply secp_group_power_pos_correct.
   + rewrite secp_group_endo_positive_power;apply secp_group_power_pos_correct.
 - lia.
Qed.
Lemma secp_group_power_multiply point n m:0<=n ->0<=m ->
 EGroup.gpow point secp_curve_group (n*m)=
 EGroup.gpow (EGroup.gpow point secp_curve_group n) secp_curve_group m.
Proof.
 apply (EGroup.gpow_gpow secp_group_point secp_group_add point secp_curve_group).
 exact (secp_group_points_complete point).
Qed.
Local Opaque secp_group_power_pos.
Theorem secp_group_lambda_action (point:secp_group_point):
 secp_group_endomorphism point=EGroup.gpow point secp_curve_group canonical_lambda_value.
Proof.
 destruct (secp_group_generator_spans point) as [k [Range Value]].
 rewrite Value,secp_group_endo_power by lia.
 rewrite <-secp_group_lambda_generator.
 pose proof canonical_lambda_value_range as LambdaRange.
 transitivity (EGroup.gpow secp_group_generator secp_curve_group (canonical_lambda_value*k)).
 - symmetry;apply secp_group_power_multiply;lia.
 - replace (canonical_lambda_value*k) with (k*canonical_lambda_value) by ring.
   apply secp_group_power_multiply;lia.
Qed.

(** CoqPrime's ordinary-projective operations are used only to check the
    abstract group-order certificate, not as a substitute for C Jacobians. *)
From Coq Require Import ZArith.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_fe_math
 C.jet_secp_canonical_scalar.
Require Import C.jet_secp_curve_group_power.
From Coqprime Require Import EGroup.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_group_projective:=SMain.pelt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
 (GZnZ.zero feP) secp_group_seven.
Fixpoint secp_group_projective_power (point:secp_group_projective) (k:positive):secp_group_projective:=
 match k with
 | xH=>point
 | xO j=>SMain.pdouble secp_group_theory (secp_group_projective_power point j)
 | xI j=>SMain.padd secp_group_theory point
    (SMain.pdouble secp_group_theory (secp_group_projective_power point j))
 end.
Lemma secp_group_projective_power_correct point k:
 SMain.pe2e secp_group_theory (secp_group_projective_power point k)=
 secp_group_power_pos (SMain.pe2e secp_group_theory point) k.
Proof.
 induction k as [k IH|k IH|];cbn [secp_group_projective_power secp_group_power_pos].
 - rewrite SMain.pe2e_add,SMain.pe2e_double,IH;reflexivity.
 - rewrite SMain.pe2e_double,IH;reflexivity.
 - reflexivity.
Qed.
Definition secp_group_generator_projective:secp_group_projective.
Proof.
 refine (SMain.mk_pelt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
  (GZnZ.zero feP) secp_group_seven secp_group_generator_x secp_group_generator_y (GZnZ.one feP) _).
 apply GZnZ.zirr;vm_compute;reflexivity.
Defined.
Lemma secp_group_generator_projective_value:
 SMain.pe2e secp_group_theory secp_group_generator_projective=secp_group_generator.
Proof.
 unfold secp_group_generator_projective,SMain.pe2e.
 destruct (SMain.Kdec secp_group_theory (GZnZ.one feP) (GZnZ.zero feP)) as [Bad|Good].
 - exfalso;pose proof (f_equal (GZnZ.val feP) Bad) as Wrong;vm_compute in Wrong;discriminate.
 - unfold secp_group_generator;eapply (SMain.curve_elt_irr secp_group_theory);
   apply (SMain.Kdiv1 secp_group_theory).
Qed.

(** The checked integer-coordinate calculation measured about 19 seconds;
    its 60-second command bound is scoped to this closed certificate. *)
Lemma secp_group_projective_zero_infinity (point:secp_group_projective):
 GZnZ.val feP (SMain.z point)=0 ->SMain.pe2e secp_group_theory point=secp_group_infinity.
Proof.
 destruct point as [x y z Curve];intro Zero;change (GZnZ.val feP z=0) in Zero;unfold SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test z)) as [b Test];destruct b;[reflexivity|].
 exfalso;unfold secp_group_zero_test in Test;rewrite Zero in Test;discriminate.
Qed.
Set Default Timeout 60.
Theorem secp_generator_order_z:
 GZnZ.val feP (SMain.z (secp_group_projective_power secp_group_generator_projective
  (Z.to_pos canonical_group_order)))=0.
Proof. vm_compute;reflexivity. Qed.
Set Default Timeout 10.
Theorem secp_generator_order_multiple:
 EGroup.gpow secp_group_generator secp_curve_group canonical_group_order=secp_group_infinity.
Proof.
 pose proof (secp_group_projective_zero_infinity
  (secp_group_projective_power secp_group_generator_projective (Z.to_pos canonical_group_order))
  secp_generator_order_z) as Zero.
 rewrite secp_group_projective_power_correct,secp_group_generator_projective_value,
  secp_group_power_pos_correct in Zero.
 change (EGroup.gpow secp_group_generator secp_curve_group canonical_group_order=secp_group_infinity) in Zero.
 exact Zero.
Qed.

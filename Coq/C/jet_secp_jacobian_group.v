(** Interpret genuine Jacobian coordinates through ordinary projective points.
    The map is (X,Y,Z) -> (XZ,Y,Z^3); no coordinate convention is identified
    without a proof. Operations will use this interpretation. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_curve_group_sign C.jet_secp_curve_group_certificate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_group_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Notation "x + y" := (GZnZ.add feP x y).
Local Notation "x * y" := (GZnZ.mul feP x y).
Local Notation "x - y" := (GZnZ.sub feP x y).
Local Notation "x / y" := (GZnZ.div feP x y).
Local Notation "- x" := (GZnZ.opp feP x).
Local Notation "0" := (GZnZ.zero feP).
Local Notation "1" := (GZnZ.one feP).
Definition secp_jacobian_curve (x y z:secp_group_field):=y*y=x*x*x+secp_group_seven*((z*z*z)*(z*z*z)).
Definition secp_jacobian_projective (x y z:secp_group_field) (Curve:secp_jacobian_curve x y z):
 secp_group_projective.
Proof.
 refine (SMain.mk_pelt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
  (GZnZ.zero feP) secp_group_seven (x*z) y (z*z*z) _).
 cbn [SMain.pow];unfold secp_jacobian_curve in Curve;rewrite Curve;ring.
Defined.
Definition secp_jacobian_group_value (x y z:secp_group_field) (Curve:secp_jacobian_curve x y z):=
 SMain.pe2e secp_group_theory (secp_jacobian_projective x y z Curve).
Lemma secp_jacobian_projective_irrelevance (x y z:secp_group_field)
 (C1 C2:secp_jacobian_curve x y z):
 secp_jacobian_projective x y z C1=secp_jacobian_projective x y z C2.
Proof. apply (SMain.curve_pelt_irr secp_group_theory);reflexivity. Qed.
Lemma secp_projective_zero_iff (p:secp_group_projective):
 SMain.pe2e secp_group_theory p=secp_group_infinity <->SMain.z p=0.
Proof.
 destruct p as [x y z Curve];unfold SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test z)) as [b Test];destruct b.
 - split;intro H;[|reflexivity].
   apply (proj1 (SMain.is_zero_correct secp_group_theory z));exact Test.
 - split;intro H;[discriminate|].
   cbn [SMain.z] in H.
   pose proof (proj2 (SMain.is_zero_correct secp_group_theory z) H) as Bad.
   rewrite Test in Bad;discriminate.
Qed.
Lemma secp_jacobian_group_infinity_iff x y z Curve:
 secp_jacobian_group_value x y z Curve=secp_group_infinity <->z=0.
Proof.
 unfold secp_jacobian_group_value;rewrite secp_projective_zero_iff.
 change (z*z*z=0 <->z=0);split.
 - intro Product;destruct (SMain.Kmult_integral secp_group_theory (z*z) z Product) as [Pair|Zero];[|exact Zero].
   destruct (SMain.Kmult_integral secp_group_theory z z Pair);assumption.
 - intro Zero;rewrite Zero;ring.
Qed.
Lemma secp_field_ratio_cross (x1 y1 x2 y2:secp_group_field):
 y1<>0 ->y2<>0 ->x1*y2=x2*y1 ->x1/y1=x2/y2.
Proof.
 intros N1 N2 Cross.
 transitivity ((x1*y2)/(y1*y2)).
 - field;split;assumption.
 - rewrite Cross;field;split;assumption.
Qed.
Lemma secp_projective_group_equal (p q:secp_group_projective):
 (SMain.z p=0 <->SMain.z q=0) ->
 SMain.x p*SMain.z q=SMain.x q*SMain.z p ->
 SMain.y p*SMain.z q=SMain.y q*SMain.z p ->
 SMain.pe2e secp_group_theory p=SMain.pe2e secp_group_theory q.
Proof.
 destruct p as [px py pz Pc],q as [qx qy qz Qc].
 cbn [SMain.x SMain.y SMain.z];intros Zero X Y;unfold SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test pz)) as [bp Tp];destruct bp;
 destruct (SMain.wb (secp_group_zero_test qz)) as [bq Tq];destruct bq;[reflexivity| | |].
 - exfalso.
   pose proof (proj1 (SMain.is_zero_correct secp_group_theory pz) Tp) as Pzero.
   pose proof (proj2 (SMain.is_zero_correct secp_group_theory qz) (proj1 Zero Pzero)) as Bad.
   congruence.
 - exfalso.
   pose proof (proj1 (SMain.is_zero_correct secp_group_theory qz) Tq) as Qzero.
   pose proof (proj2 (SMain.is_zero_correct secp_group_theory pz) (proj2 Zero Qzero)) as Bad.
   congruence.
 - assert (Pnonzero:pz<>0).
   { intro E;pose proof (proj2 (SMain.is_zero_correct secp_group_theory pz) E);congruence. }
   assert (Qnonzero:qz<>0).
   { intro E;pose proof (proj2 (SMain.is_zero_correct secp_group_theory qz) E);congruence. }
   apply (SMain.curve_elt_irr secp_group_theory);apply secp_field_ratio_cross;assumption.
Qed.
Lemma secp_jacobian_curve_rescale x y z (Curve:secp_jacobian_curve x y z) (s:secp_group_field):
 secp_jacobian_curve (x*(s*s)) (y*(s*s*s)) (z*s).
Proof.
 unfold secp_jacobian_curve in *.
 replace (y*(s*s*s)*(y*(s*s*s))) with ((y*y)*((s*s*s)*(s*s*s))) by ring.
 rewrite Curve;ring.
Qed.
Lemma secp_jacobian_group_rescale x y z (Curve:secp_jacobian_curve x y z) (s:secp_group_field):
 s<>0 ->secp_jacobian_group_value (x*(s*s)) (y*(s*s*s)) (z*s)
  (secp_jacobian_curve_rescale x y z Curve s)=secp_jacobian_group_value x y z Curve.
Proof.
 intro Nonzero;unfold secp_jacobian_group_value.
 apply secp_projective_group_equal;cbn [secp_jacobian_projective SMain.x SMain.y SMain.z].
 - split;intro Zero.
   + destruct (SMain.Kmult_integral secp_group_theory ((z*s)*(z*s)) (z*s) Zero) as [Pair|Single].
     * destruct (SMain.Kmult_integral secp_group_theory (z*s) (z*s) Pair) as [Left|Right].
       -- destruct (SMain.Kmult_integral secp_group_theory z s Left);[subst z;ring|contradiction].
       -- destruct (SMain.Kmult_integral secp_group_theory z s Right);[subst z;ring|contradiction].
     * destruct (SMain.Kmult_integral secp_group_theory z s Single);[subst z;ring|contradiction].
   + destruct (SMain.Kmult_integral secp_group_theory (z*z) z Zero) as [Pair|Single].
     * destruct (SMain.Kmult_integral secp_group_theory z z Pair);subst z;ring.
     * subst z;ring.
 - ring.
 - ring.
Qed.
Lemma secp_jacobian_curve_negate x y z (Curve:secp_jacobian_curve x y z):
 secp_jacobian_curve x (-y) z.
Proof.
 unfold secp_jacobian_curve in *.
 replace (-y*(-y)) with (y*y) by ring;exact Curve.
Qed.
Lemma secp_jacobian_group_negate x y z (Curve:secp_jacobian_curve x y z):
 secp_jacobian_group_value x (-y) z (secp_jacobian_curve_negate x y z Curve)=
 SMain.opp secp_group_theory (secp_jacobian_group_value x y z Curve).
Proof.
 unfold secp_jacobian_group_value,secp_jacobian_projective,SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test (z*z*z))) as [b Test];destruct b;[reflexivity|].
 cbn [SMain.opp];apply (SMain.curve_elt_irr secp_group_theory);[reflexivity|].
 assert (Nz:z*z*z<>0).
 { intro E;pose proof (proj2 (SMain.is_zero_correct secp_group_theory (z*z*z)) E);congruence. }
 assert (Znonzero:z<>0) by (intro E;apply Nz;rewrite E;ring).
 field;exact Znonzero.
Qed.

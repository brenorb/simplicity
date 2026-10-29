(** Group semantics of the exact mixed-addition field formulas with a shared-Z
    context. Equal and inverse branches retain their original conditions.
    Literal word dispatch and the extended ratio bridge are separate. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_jacobian_group C.jet_secp_jacobian_double_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_mixed_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Notation "x + y" := (GZnZ.add feP x y).
Local Notation "x * y" := (GZnZ.mul feP x y).
Local Notation "x - y" := (GZnZ.sub feP x y).
Local Notation "x / y" := (GZnZ.div feP x y).
Local Notation "- x" := (GZnZ.opp feP x).
Local Notation "0" := (GZnZ.zero feP).
Local Notation "1" := (GZnZ.one feP).
Definition secp_jmixed_h (x z bx:secp_group_field):=x-bx*(z*z).
Definition secp_jmixed_i (y z byword:secp_group_field):=y-byword*(z*z*z).
Definition secp_jmixed_x (h i x:secp_group_field):=h*h*h-(1+1)*(h*h*x)+i*i.
Definition secp_jmixed_y (h i x y:secp_group_field):=h*h*h*y+i*(secp_jmixed_x h i x-h*h*x).
Lemma secp_jacobian_mixed_curve (c x y z bx byword:secp_group_field)
 (A:secp_jacobian_curve x y (c*z)) (B:secp_jacobian_curve bx byword c):
 let h:=secp_jmixed_h x z bx in let i:=secp_jmixed_i y z byword in
 secp_jacobian_curve (secp_jmixed_x h i x) (secp_jmixed_y h i x y) (c*(-h*z)).
Proof.
 cbn zeta;unfold secp_jacobian_curve in *.
 unfold secp_jmixed_y,secp_jmixed_x,secp_jmixed_h,secp_jmixed_i,secp_group_field in *.
 ring [A B].
Qed.
Lemma secp_jmixed_x_difference (c x z bx:secp_group_field):c<>0 ->z<>0 ->
 bx/(c*c)-x/((c*z)*(c*z))= -(secp_jmixed_h x z bx)/(c*c*z*z).
Proof.
 intros C Z;unfold secp_jmixed_h,secp_group_field in *;field;split;assumption.
Qed.
Lemma secp_jmixed_y_difference (c y z byword:secp_group_field):c<>0 ->z<>0 ->
 byword/(c*c*c)-y/((c*z)*(c*z)*(c*z))= -(secp_jmixed_i y z byword)/(c*c*c*z*z*z).
Proof.
 intros C Z;unfold secp_jmixed_i,secp_group_field in *;field;split;assumption.
Qed.
Lemma secp_jmixed_slope (c x y z bx byword:secp_group_field):c<>0 ->z<>0 ->secp_jmixed_h x z bx<>0 ->
 (byword/(c*c*c)-y/((c*z)*(c*z)*(c*z)))/(bx/(c*c)-x/((c*z)*(c*z)))=
 secp_jmixed_i y z byword/(c*z*secp_jmixed_h x z bx).
Proof.
 intros C Z H;rewrite secp_jmixed_x_difference,secp_jmixed_y_difference by assumption.
 unfold secp_group_field in *;field;repeat split;try assumption.
 intro Zero;apply H;ring [Zero].
Qed.
Lemma secp_jmixed_affine_x (c x y z bx byword:secp_group_field):
 c<>0 ->z<>0 ->secp_jmixed_h x z bx<>0 ->
 let h:=secp_jmixed_h x z bx in let i:=secp_jmixed_i y z byword in
 secp_jmixed_x h i x/((c*(-h*z))*(c*(-h*z)))=
 (i/(c*z*h))*(i/(c*z*h))-x/((c*z)*(c*z))-bx/(c*c).
Proof.
 intros C Z H;cbn zeta.
 unfold secp_jmixed_x,secp_jmixed_h,secp_group_field in *.
 field;repeat split;try assumption.
 intro Zero;apply H.
 transitivity (-(-(x-bx*(z*z))));[ring|].
 rewrite Zero;ring.
Qed.
Lemma secp_jmixed_affine_y (c x y z bx byword:secp_group_field):
 c<>0 ->z<>0 ->secp_jmixed_h x z bx<>0 ->
 let h:=secp_jmixed_h x z bx in let i:=secp_jmixed_i y z byword in
 secp_jmixed_y h i x y/((c*(-h*z))*(c*(-h*z))*(c*(-h*z)))=
 - (y/((c*z)*(c*z)*(c*z)))-(i/(c*z*h))*
 (secp_jmixed_x h i x/((c*(-h*z))*(c*(-h*z)))-x/((c*z)*(c*z))).
Proof.
 intros C Z H;cbn zeta.
 unfold secp_jmixed_y,secp_jmixed_x,secp_jmixed_h,secp_group_field in *.
 field;repeat split;try assumption.
 intro Zero;apply H.
 transitivity (-(-(x-bx*(z*z))));[ring|].
 rewrite Zero;ring.
Qed.
Require Import C.jet_secp_jacobian_affine_group.
Lemma secp_jacobian_mixed_finite_group (c x y z bx byword:secp_group_field)
 (A:secp_jacobian_curve x y (c*z)) (B:secp_jacobian_curve bx byword c):
 c<>0 ->z<>0 ->secp_jmixed_h x z bx<>0 ->
 let h:=secp_jmixed_h x z bx in let i:=secp_jmixed_i y z byword in
 secp_jacobian_group_value (secp_jmixed_x h i x) (secp_jmixed_y h i x y) (c*(-h*z))
  (secp_jacobian_mixed_curve c x y z bx byword A B)=
 SMain.add secp_group_theory (secp_jacobian_group_value x y (c*z) A)
  (secp_jacobian_group_value bx byword c B).
Proof.
 intros C Z H;cbn zeta.
 assert (NegH: -(secp_jmixed_h x z bx)<>0).
 { intro Zero;apply H;unfold secp_group_field in *;ring [Zero]. }
 assert (InNZ:c*z<>0) by (apply (SMain.Kmult_integral_contrapositive secp_group_theory);assumption).
 assert (OutNZ:c*(-secp_jmixed_h x z bx*z)<>0).
 { repeat apply (SMain.Kmult_integral_contrapositive secp_group_theory);assumption. }
 rewrite (secp_jacobian_affine_value _ _ _ _ OutNZ),
  (secp_jacobian_affine_value _ _ _ A InNZ),(secp_jacobian_affine_value _ _ _ B C).
 unfold SMain.add.
 destruct (SMain.Kdec secp_group_theory (x/((c*z)*(c*z))) (bx/(c*c))) as [Same|Different].
 - exfalso;apply H.
   assert (Difference:bx/(c*c)-x/((c*z)*(c*z))=0) by (rewrite Same;ring).
   rewrite secp_jmixed_x_difference in Difference by assumption.
   assert (DenNZ:c*c*z*z<>0) by (repeat apply (SMain.Kmult_integral_contrapositive secp_group_theory);assumption).
   pose proof (SMain.Kdiv_inv_eq_0 secp_group_theory _ Difference DenNZ) as Zero.
   unfold secp_group_field in *;ring [Zero].
 - apply (SMain.curve_elt_irr secp_group_theory);cbn [SMain.pow];
    rewrite secp_jmixed_slope by assumption.
   + apply secp_jmixed_affine_x;assumption.
   + rewrite <-(secp_jmixed_affine_x c x y z bx byword C Z H).
     apply secp_jmixed_affine_y;assumption.
Qed.
Lemma secp_jacobian_context_scaled (c x y z bx byword:secp_group_field)
 (A:secp_jacobian_curve x y (c*z)) (B:secp_jacobian_curve bx byword c):
 z<>0 ->x=bx*(z*z) ->y=byword*(z*z*z) ->
 secp_jacobian_group_value x y (c*z) A=secp_jacobian_group_value bx byword c B.
Proof.
 intros Z X Y.
 transitivity (secp_jacobian_group_value (bx*(z*z)) (byword*(z*z*z)) (c*z)
  (secp_jacobian_curve_rescale bx byword c B z)).
 - apply secp_jacobian_group_value_ext;[exact X|exact Y|reflexivity].
 - apply secp_jacobian_group_rescale;exact Z.
Qed.
Lemma secp_jacobian_mixed_equal_group (c x y z bx byword:secp_group_field)
 (A:secp_jacobian_curve x y (c*z)) (B:secp_jacobian_curve bx byword c):
 z<>0 ->secp_jmixed_h x z bx=0 ->secp_jmixed_i y z byword=0 ->
 secp_jacobian_group_value x y (c*z) A=secp_jacobian_group_value bx byword c B.
Proof.
 intros Z H I;apply secp_jacobian_context_scaled;[exact Z| |].
 - apply (SMain.Keq_minus_eq secp_group_theory);exact H.
 - apply (SMain.Keq_minus_eq secp_group_theory);exact I.
Qed.
Lemma secp_jacobian_mixed_opposite_y (c x y z bx byword:secp_group_field)
 (A:secp_jacobian_curve x y (c*z)) (B:secp_jacobian_curve bx byword c):
 secp_jmixed_h x z bx=0 ->secp_jmixed_i y z byword<>0 ->y= -(byword*(z*z*z)).
Proof.
 intros H I.
 assert (X:x=bx*(z*z)) by (apply (SMain.Keq_minus_eq secp_group_theory);exact H).
 assert (Squares:SMain.pow (GZnZ.one feP) (GZnZ.mul feP) y 2=
  SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (byword*(z*z*z)) 2).
 { cbn [SMain.pow];unfold secp_jacobian_curve,secp_group_field in *;rewrite A.
   ring [B X]. }
 destruct (SMain.Ksqr_eq secp_group_theory y (byword*(z*z*z)) Squares) as [Same|Opposite];[|exact Opposite].
 exfalso;apply I;unfold secp_jmixed_i;rewrite Same;ring.
Qed.
Lemma secp_jacobian_mixed_inverse_group (c x y z bx byword:secp_group_field)
 (A:secp_jacobian_curve x y (c*z)) (B:secp_jacobian_curve bx byword c):
 z<>0 ->secp_jmixed_h x z bx=0 ->secp_jmixed_i y z byword<>0 ->
 secp_jacobian_group_value x y (c*z) A=
 SMain.opp secp_group_theory (secp_jacobian_group_value bx byword c B).
Proof.
 intros Z H I.
 pose proof (secp_jacobian_mixed_opposite_y c x y z bx byword A B H I) as Y.
 assert (X:x=bx*(z*z)) by (apply (SMain.Keq_minus_eq secp_group_theory);exact H).
 transitivity (secp_jacobian_group_value bx (-byword) c (secp_jacobian_curve_negate bx byword c B)).
 - apply secp_jacobian_context_scaled;[exact Z|exact X|].
   rewrite Y;unfold secp_group_field;ring.
 - apply secp_jacobian_group_negate.
Qed.

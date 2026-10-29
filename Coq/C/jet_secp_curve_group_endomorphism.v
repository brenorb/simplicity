(** The actual beta field constant preserves the curve and affine addition.
    This is the group homomorphism needed by the GLV/Strauss adapter; it does
    not yet interpret the C Jacobian operations or their window traversal. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_curve_group_sign C.jet_secp_beta_global.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_group_beta:secp_group_field:=GZnZ.mkznz feP beta_value eq_refl.
Add Field secp_group_field_theory : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Notation "x + y" := (GZnZ.add feP x y).
Local Notation "x * y" := (GZnZ.mul feP x y).
Local Notation "x - y" := (GZnZ.sub feP x y).
Local Notation "x / y" := (GZnZ.div feP x y).
Local Notation "- x" := (GZnZ.opp feP x).
Local Notation "0" := (GZnZ.zero feP).
Local Notation "1" := (GZnZ.one feP).
Lemma secp_group_beta_cube:secp_group_beta*secp_group_beta*secp_group_beta=1.
Proof. apply GZnZ.zirr;vm_compute;reflexivity. Qed.
Lemma secp_group_beta_nonzero:secp_group_beta<>0.
Proof. intro Bad;pose proof (f_equal (GZnZ.val feP) Bad) as V;vm_compute in V;discriminate. Qed.
Lemma secp_group_beta_cube_scale (x:secp_group_field):
 (secp_group_beta*x)*(secp_group_beta*x)*(secp_group_beta*x)=x*x*x.
Proof.
 transitivity ((secp_group_beta*secp_group_beta*secp_group_beta)*(x*x*x));[ring|].
 rewrite secp_group_beta_cube;ring.
Qed.
Lemma secp_group_beta_four_square (t:secp_group_field):
 (secp_group_beta*secp_group_beta*t)*(secp_group_beta*secp_group_beta*t)=secp_group_beta*(t*t).
Proof.
 transitivity ((secp_group_beta*secp_group_beta*secp_group_beta)*(secp_group_beta*(t*t)));[ring|].
 rewrite secp_group_beta_cube;ring.
Qed.
Lemma secp_group_beta_tangent_slope (x y:secp_group_field):y<>0 ->
 ((1+1+1)*(secp_group_beta*x)*(secp_group_beta*x)+0)/((1+1)*y)=
 secp_group_beta*secp_group_beta*(((1+1+1)*x*x+0)/((1+1)*y)).
Proof.
 intro Nz;field;split;[exact Nz|exact (SMain.two_not_zero secp_group_theory)].
Qed.
Lemma secp_group_beta_tangent_x (x y:secp_group_field):y<>0 ->
 (((1+1+1)*(secp_group_beta*x)*(secp_group_beta*x)+0)/((1+1)*y))*
 (((1+1+1)*(secp_group_beta*x)*(secp_group_beta*x)+0)/((1+1)*y))-(1+1)*(secp_group_beta*x)=
 secp_group_beta*((((1+1+1)*x*x+0)/((1+1)*y))*(((1+1+1)*x*x+0)/((1+1)*y))-(1+1)*x).
Proof.
 intro Nz;rewrite secp_group_beta_tangent_slope by exact Nz.
 rewrite secp_group_beta_four_square;ring.
Qed.
Lemma secp_group_beta_tangent_y (x y:secp_group_field):y<>0 ->
 -y-(((1+1+1)*(secp_group_beta*x)*(secp_group_beta*x)+0)/((1+1)*y))*
  (((((1+1+1)*(secp_group_beta*x)*(secp_group_beta*x)+0)/((1+1)*y))*
    (((1+1+1)*(secp_group_beta*x)*(secp_group_beta*x)+0)/((1+1)*y))-
    (1+1)*(secp_group_beta*x))-(secp_group_beta*x))=
 -y-(((1+1+1)*x*x+0)/((1+1)*y))*
  (((((1+1+1)*x*x+0)/((1+1)*y))*(((1+1+1)*x*x+0)/((1+1)*y))-(1+1)*x)-x).
Proof.
 intro Nz;rewrite secp_group_beta_tangent_x by exact Nz.
 rewrite secp_group_beta_tangent_slope by exact Nz.
 set (l:=((1+1+1)*x*x+0)/((1+1)*y)).
 replace (secp_group_beta*secp_group_beta*l*(secp_group_beta*(l*l-(1+1)*x)-secp_group_beta*x))
 with ((secp_group_beta*secp_group_beta*secp_group_beta)*(l*(l*l-(1+1)*x-x))) by ring.
 rewrite secp_group_beta_cube;ring.
Qed.
Lemma secp_group_beta_secant_slope (x1 x2 y1 y2:secp_group_field):x2-x1<>0 ->
 (y2-y1)/(secp_group_beta*x2-secp_group_beta*x1)=
 secp_group_beta*secp_group_beta*((y2-y1)/(x2-x1)).
Proof.
 intro Nz.
 transitivity ((secp_group_beta*secp_group_beta*secp_group_beta)*
  ((y2-y1)/(secp_group_beta*x2-secp_group_beta*x1))).
 - rewrite secp_group_beta_cube;ring.
 - field;repeat split;try exact Nz;try exact secp_group_beta_nonzero.
   replace (secp_group_beta*x2-secp_group_beta*x1) with (secp_group_beta*(x2-x1)) by ring.
   apply (SMain.Kmult_integral_contrapositive secp_group_theory);[exact secp_group_beta_nonzero|exact Nz].
Qed.
Lemma secp_group_beta_secant_x (x1 x2 y1 y2:secp_group_field):x2-x1<>0 ->
 ((y2-y1)/(secp_group_beta*x2-secp_group_beta*x1))*
 ((y2-y1)/(secp_group_beta*x2-secp_group_beta*x1))-secp_group_beta*x1-secp_group_beta*x2=
 secp_group_beta*(((y2-y1)/(x2-x1))*((y2-y1)/(x2-x1))-x1-x2).
Proof.
 intro Nz;rewrite secp_group_beta_secant_slope by exact Nz.
 rewrite secp_group_beta_four_square;ring.
Qed.
Lemma secp_group_beta_secant_y (x1 x2 y1 y2:secp_group_field):x2-x1<>0 ->
 -y1-((y2-y1)/(secp_group_beta*x2-secp_group_beta*x1))*
  ((((y2-y1)/(secp_group_beta*x2-secp_group_beta*x1))*
    ((y2-y1)/(secp_group_beta*x2-secp_group_beta*x1))-
    secp_group_beta*x1-secp_group_beta*x2)-secp_group_beta*x1)=
 -y1-((y2-y1)/(x2-x1))*
  ((((y2-y1)/(x2-x1))*((y2-y1)/(x2-x1))-x1-x2)-x1).
Proof.
 intro Nz;rewrite secp_group_beta_secant_x by exact Nz.
 rewrite secp_group_beta_secant_slope by exact Nz.
 set (l:=(y2-y1)/(x2-x1)).
 replace (secp_group_beta*secp_group_beta*l*(secp_group_beta*(l*l-x1-x2)-secp_group_beta*x1))
 with ((secp_group_beta*secp_group_beta*secp_group_beta)*(l*(l*l-x1-x2-x1))) by ring.
 rewrite secp_group_beta_cube;ring.
Qed.
Lemma secp_group_beta_cancel (x y:secp_group_field):secp_group_beta*x=secp_group_beta*y ->x=y.
Proof.
 intro E.
 pose proof (f_equal (fun z=>z/secp_group_beta) E) as V.
 assert (Left:(secp_group_beta*x)/secp_group_beta=x) by (field;exact secp_group_beta_nonzero).
 assert (Right:(secp_group_beta*y)/secp_group_beta=y) by (field;exact secp_group_beta_nonzero).
 exact (eq_trans (eq_sym Left) (eq_trans V Right)).
Qed.
Lemma secp_group_endo_curve x y:
 SMain.pow (GZnZ.one feP) (GZnZ.mul feP) y 2=
 GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) x 3)
  (GZnZ.mul feP (GZnZ.zero feP) x)) secp_group_seven ->
 SMain.pow (GZnZ.one feP) (GZnZ.mul feP) y 2=
 GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_group_beta*x) 3)
  (GZnZ.mul feP (GZnZ.zero feP) (secp_group_beta*x))) secp_group_seven.
Proof.
 cbn [SMain.pow];intro Curve;rewrite Curve.
 replace ((secp_group_beta*x)*((secp_group_beta*x)*(secp_group_beta*x))) with (x*(x*x));[ring|].
 transitivity (x*x*x);[ring|].
 rewrite <-(secp_group_beta_cube_scale x);ring.
Qed.
Definition secp_group_endomorphism (point:secp_group_point):secp_group_point:=
 match point with
 | SMain.inf_elt _ _ _ _ _=>secp_group_infinity
 | SMain.curve_elt _ _ _ _ _ x y Curve=>
  SMain.curve_elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
   (GZnZ.zero feP) secp_group_seven (secp_group_beta*x) y (secp_group_endo_curve x y Curve)
 end.
Lemma secp_group_endo_add (p q:secp_group_point):
 secp_group_endomorphism (SMain.add secp_group_theory p q)=
 SMain.add secp_group_theory (secp_group_endomorphism p) (secp_group_endomorphism q).
Proof.
 destruct p as [|x1 y1 H1],q as [|x2 y2 H2];try reflexivity.
 unfold SMain.add;cbn [secp_group_endomorphism].
 destruct (SMain.Kdec secp_group_theory x1 x2) as [Same|Different];
 destruct (SMain.Kdec secp_group_theory (secp_group_beta*x1) (secp_group_beta*x2)) as [SameBeta|DifferentBeta].
 - destruct (SMain.Kdec secp_group_theory y1 (-y2)) as [Inverse|NotInverse];[reflexivity|].
   pose proof (SMain.add_zero_diff secp_group_theory y2 Same H1 H2 NotInverse) as Nz.
   cbn [secp_group_endomorphism].
   apply (SMain.curve_elt_irr secp_group_theory);cbn [SMain.pow].
   + symmetry;apply secp_group_beta_tangent_x;exact Nz.
   + symmetry;apply secp_group_beta_tangent_y;exact Nz.
 - exfalso;apply DifferentBeta;rewrite Same;reflexivity.
 - exfalso;apply Different;apply secp_group_beta_cancel;exact SameBeta.
 - assert (Nz:x2-x1<>0).
   { apply (SMain.Kdiff_diff_minus_eq secp_group_theory);congruence. }
   cbn [secp_group_endomorphism].
   apply (SMain.curve_elt_irr secp_group_theory);cbn [SMain.pow].
   + symmetry;apply secp_group_beta_secant_x;exact Nz.
   + symmetry;apply secp_group_beta_secant_y;exact Nz.
Qed.

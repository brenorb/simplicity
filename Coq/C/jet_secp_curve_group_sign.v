(** The fixed curve has no nonidentity point fixed by affine negation.
    Needed for odd cardinality, not an additional jet-domain premise. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_curve_nonzero C.jet_secp_curve_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_group_point:=SMain.elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
 (GZnZ.zero feP) secp_group_seven.
Definition secp_group_infinity:secp_group_point:=SMain.inf_elt _ _ _ _ _.
Lemma secp_group_curve_numeric (x y:secp_group_field):
 SMain.pow (GZnZ.one feP) (GZnZ.mul feP) y 2=
 GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) x 3)
  (GZnZ.mul feP (GZnZ.zero feP) x)) secp_group_seven ->
 (GZnZ.val feP x*GZnZ.val feP x*GZnZ.val feP x+7) mod feP=
 (GZnZ.val feP y*GZnZ.val feP y) mod feP.
Proof.
 intro Curve;pose proof (f_equal (GZnZ.val feP) Curve) as Values.
 cbn [SMain.pow GZnZ.add GZnZ.mul GZnZ.zero GZnZ.val secp_group_seven] in Values.
 rewrite !Z.mod_0_l in Values by (pose proof secp_group_field_positive;lia).
 rewrite Z.add_0_r,Z.mod_mod in Values by (pose proof secp_group_field_positive;lia).
 rewrite Z.mul_mod_idemp_r,Z.add_mod_idemp_l in Values by (pose proof secp_group_field_positive;lia).
 rewrite Z.mul_assoc in Values;symmetry;exact Values.
Qed.
Lemma secp_group_field_opp_fixed (y:secp_group_field):
 GZnZ.opp feP y=y ->y=GZnZ.zero feP.
Proof.
 destruct y as [Y Reduced];intro Equal.
 pose proof (f_equal (GZnZ.val feP) Equal) as Values.
 change ((-Y) mod feP=Y) in Values.
 assert (Positive:0<feP) by exact secp_group_field_positive.
 pose proof (Z.mod_pos_bound Y feP Positive) as Range;rewrite <-Reduced in Range.
 assert (Zero:Y=0).
 { destruct (Z.eq_dec Y 0) as [Zer|Nonzero];[exact Zer|].
   assert (Neg:(-Y) mod feP=feP-Y).
   { symmetry;apply Z.mod_unique with (q:= -1);[left;lia|ring]. }
   rewrite Neg in Values.
   assert (Odd:exists k,feP=2*k+1).
   { exists ((feP-1)/2);vm_compute;reflexivity. }
   destruct Odd as [k Odd];lia. }
 apply GZnZ.zirr;change (Y=0);exact Zero.
Qed.
Theorem secp_group_negation_fixed (point:secp_group_point):
 SMain.opp secp_group_theory point=point ->point=secp_group_infinity.
Proof.
 destruct point as [|x y Curve];[reflexivity|].
 intro Equal.
 pose proof (f_equal (fun p:secp_group_point=>match p with
  | SMain.inf_elt _ _ _ _ _=>GZnZ.zero feP
  | SMain.curve_elt _ _ _ _ _ _ yy _=>yy end) Equal) as YEqual.
 change (GZnZ.opp feP y=y) in YEqual.
 pose proof (secp_group_field_opp_fixed y YEqual) as Zero.
 pose proof (secp_group_curve_numeric x y Curve) as Numeric.
 rewrite Zero in Numeric.
 change ((GZnZ.val feP x*GZnZ.val feP x*GZnZ.val feP x+7) mod feP=(0*0) mod feP) in Numeric.
 pose proof (secp_curve_y_nonzero (GZnZ.val feP x) 0 Numeric) as Nonzero.
 exfalso;apply Nonzero;reflexivity.
Qed.

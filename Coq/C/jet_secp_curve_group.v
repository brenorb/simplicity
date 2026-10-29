(** The existing CoqPrime affine group instantiated at the fixed secp curve.
    No order n, endomorphism action or Jacobian execution bridge is assumed. *)
From Coq Require Import ZArith Lia List.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime.PrimalityTest Require Import FGroup.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma secp_group_field_positive:0<feP.
Proof. unfold feP,feR;lia. Qed.
Definition secp_group_field:=GZnZ.znz feP.
Definition secp_group_seven:secp_group_field:=GZnZ.mkznz feP 7 eq_refl.
Definition secp_group_zero_test (x:secp_group_field):=Z.eqb (GZnZ.val feP x) 0.
Definition secp_group_theory:SMain.ell_theory
 (GZnZ.zero feP) (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP) (GZnZ.sub feP)
 (GZnZ.opp feP) (GZnZ.inv feP) (GZnZ.div feP)
 (GZnZ.zero feP) secp_group_seven secp_group_zero_test.
Proof.
 refine {|SMain.Kfth:=GZnZ.FZpZ feP secp256k1_field_prime|}.
 - intro Equal;pose proof (f_equal (GZnZ.val feP) Equal) as Values.
   vm_compute in Values;discriminate.
 - intro Equal;pose proof (f_equal (GZnZ.val feP) Equal) as Values.
   vm_compute in Values;discriminate.
 - intro Equal;pose proof (f_equal (GZnZ.val feP) Equal) as Values.
   vm_compute in Values;discriminate.
 - intros [x Bound];unfold secp_group_zero_test;cbn [GZnZ.val];split.
   + intro Zero;apply Z.eqb_eq in Zero;apply GZnZ.zirr;change (x=0);exact Zero.
   + intro Equal;apply Z.eqb_eq;pose proof (f_equal (GZnZ.val feP) Equal) as Values.
     change (x=0) in Values;exact Values.
Defined.
Definition secp_curve_group:=SMain.EFGroup secp_group_theory
 (GZnZ.uniq_all_znz feP secp_group_field_positive)
 (GZnZ.in_all_znz feP secp_group_field_positive).
Theorem secp_curve_group_order_bound:FGroup.g_order secp_curve_group<=2*feP+1.
Proof.
 pose proof (SMain.EFGroup_order secp_group_theory
 (GZnZ.uniq_all_znz feP secp_group_field_positive)
 (GZnZ.in_all_znz feP secp_group_field_positive)) as Bound.
 rewrite GZnZ.all_znz_length,inj_Zabs_nat,Z.abs_eq in Bound by (pose proof secp_group_field_positive;lia).
 exact Bound.
Qed.
Theorem secp_curve_group_order_positive:0<FGroup.g_order secp_curve_group.
Proof. apply FGroup.g_order_pos. Qed.

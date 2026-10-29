(** Odd cardinality from the proved unique fixed point of affine negation. *)
From Coq Require Import ZArith List Lia.
From Coqprime Require Import UList.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime.PrimalityTest Require Import FGroup.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_fe_math.
Require Import C.jet_finite_involution.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_group_points:=FGroup.s secp_curve_group.
Definition secp_group_nonzero_points:=tl secp_group_points.
Lemma secp_group_points_head:secp_group_points=secp_group_infinity::secp_group_nonzero_points.
Proof.
 cbv beta iota zeta delta [secp_group_points secp_group_nonzero_points secp_curve_group
   FGroup.s SMain.EFGroup SMain.FELLK tl secp_group_infinity].
 reflexivity.
Qed.
Local Lemma ulist_nodup {A:Set} (l:list A):UList.ulist l ->NoDup l.
Proof. intro Unique;induction Unique;constructor;assumption. Qed.
Lemma secp_group_points_nodup:NoDup secp_group_points.
Proof. apply ulist_nodup;apply FGroup.unique_s. Qed.
Lemma secp_group_points_complete point:In point secp_group_points.
Proof.
 exact (SMain.FELLK_in secp_group_theory (GZnZ.all_znz feP secp_group_field_positive)
  (GZnZ.in_all_znz feP secp_group_field_positive) point).
Qed.
Lemma secp_group_order_points:FGroup.g_order secp_curve_group=Z.of_nat (length secp_group_points).
Proof. reflexivity. Qed.
Local Opaque secp_group_points secp_group_nonzero_points secp_curve_group.
Theorem secp_curve_group_order_odd:Z.Odd (FGroup.g_order secp_curve_group).
Proof.
 pose proof secp_group_points_nodup as Unique.
 rewrite secp_group_points_head in Unique;apply NoDup_cons_iff in Unique.
 destruct Unique as [NotInfinity Unique].
 assert (Closed:forall point,In point secp_group_nonzero_points ->
   In (SMain.opp secp_group_theory point) secp_group_nonzero_points).
 { intros point Found;pose proof (secp_group_points_complete (SMain.opp secp_group_theory point)) as Where.
   rewrite secp_group_points_head in Where;destruct Where as [Equal|Where];[|exact Where].
   pose proof (f_equal (SMain.opp secp_group_theory) Equal) as Inverse.
   rewrite SMain.opp_opp in Inverse.
   change (secp_group_infinity=point) in Inverse.
   exfalso;apply NotInfinity;rewrite Inverse;exact Found. }
 assert (Free:forall point,In point secp_group_nonzero_points ->SMain.opp secp_group_theory point<>point).
 { intros point Found Equal;pose proof (secp_group_negation_fixed point Equal) as Zero.
   apply NotInfinity;rewrite <-Zero;exact Found. }
 destruct (fixed_point_free_involution_even (SMain.opp secp_group_theory)
  secp_group_nonzero_points Unique Closed ltac:(intros;apply SMain.opp_opp) Free) as [k K].
 rewrite secp_group_order_points.
 change (exists z:Z,Z.of_nat (length secp_group_points)=2*z+1).
 exists (Z.of_nat k);rewrite secp_group_points_head.
 cbn [length];rewrite Nat2Z.inj_succ,K,Nat2Z.inj_mul;cbn [Z.of_nat];lia.
Qed.

(** Fast positive powers and the original C group's concrete generator.
    The power certificate is computed with checked VM conversion. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup FGroup.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_odd
 C.jet_secp_fe_math C.jet_secp_canonical_scalar C.jet_secp_scalar_prime.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_group_add:=SMain.add secp_group_theory.
Fixpoint secp_group_power_pos (point:secp_group_point) (k:positive):secp_group_point:=
 match k with
 | xH=>point
 | xO j=>let q:=secp_group_power_pos point j in secp_group_add q q
 | xI j=>let q:=secp_group_power_pos point j in secp_group_add point (secp_group_add q q)
 end.
Lemma secp_group_power_add point n m:0<=n ->0<=m ->
 EGroup.gpow point secp_curve_group (n+m)=
 secp_group_add (EGroup.gpow point secp_curve_group n) (EGroup.gpow point secp_curve_group m).
Proof.
 apply (EGroup.gpow_add secp_group_point secp_group_add point secp_curve_group).
 exact (secp_group_points_complete point).
Qed.
Lemma secp_group_power_one point:EGroup.gpow point secp_curve_group 1=point.
Proof.
 apply (EGroup.gpow_1 secp_group_point secp_group_add point secp_curve_group).
 exact (secp_group_points_complete point).
Qed.
Lemma secp_group_power_pos_correct point k:secp_group_power_pos point k=
 EGroup.gpow point secp_curve_group (Z.pos k).
Proof.
 induction k as [k IH|k IH|];cbn [secp_group_power_pos].
 - replace (Z.pos k~1) with (1+(Z.pos k+Z.pos k)) by lia.
   rewrite secp_group_power_add by lia.
   rewrite secp_group_power_one,secp_group_power_add by lia.
   rewrite IH;reflexivity.
 - replace (Z.pos k~0) with (Z.pos k+Z.pos k) by lia.
   rewrite secp_group_power_add by lia;rewrite IH;reflexivity.
 - symmetry;apply secp_group_power_one.
Qed.
Definition secp_group_generator_x:secp_group_field:=GZnZ.mkznz feP
 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798 eq_refl.
Definition secp_group_generator_y:secp_group_field:=GZnZ.mkznz feP
 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 eq_refl.
Definition secp_group_generator:secp_group_point.
Proof.
 refine (SMain.curve_elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
  (GZnZ.zero feP) secp_group_seven secp_group_generator_x secp_group_generator_y _).
 apply GZnZ.zirr;vm_compute;reflexivity.
Defined.
Lemma secp_group_generator_nonzero:secp_group_generator<>secp_group_infinity.
Proof. discriminate. Qed.

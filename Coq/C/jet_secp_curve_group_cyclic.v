(** Every curve point is a scalar power of the original generator, with a
    scalar in the original canonical range. No cyclicity premise is assumed. *)
From Coq Require Import ZArith List Lia.
From Coqprime Require Import EGroup FGroup UList.
From Coqprime.elliptic Require Import SMain.
Require Import C.jet_secp_canonical_scalar C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_odd C.jet_secp_curve_group_power C.jet_secp_curve_group_order
 C.jet_secp_curve_group_certificate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_generator_powers:=EGroup.support (SMain.ceqb secp_group_theory)
 secp_group_generator secp_curve_group.
Local Opaque EGroup.support secp_curve_group secp_group_generator.
Lemma secp_generator_powers_order:Z.of_nat (length secp_generator_powers)=canonical_group_order.
Proof.
 pose proof (secp_generator_order_from_multiple secp_generator_order_multiple) as Order.
 unfold EGroup.e_order in Order;exact Order.
Qed.
Local Lemma ulist_nodup {A:Set} (l:list A):UList.ulist l ->NoDup l.
Proof. intro Unique;induction Unique;constructor;assumption. Qed.
Lemma secp_generator_powers_nodup:NoDup secp_generator_powers.
Proof.
 apply ulist_nodup.
 apply (EGroup.support_ulist secp_group_point (SMain.ceqb secp_group_theory)
  secp_group_add secp_group_generator secp_curve_group).
 exact (secp_group_points_complete secp_group_generator).
Qed.
Lemma secp_generator_powers_incl:incl secp_generator_powers secp_group_points.
Proof.
 apply (EGroup.support_incl_G secp_group_point (SMain.ceqb secp_group_theory)
  secp_group_add secp_group_generator secp_curve_group).
 exact (secp_group_points_complete secp_group_generator).
Qed.
Local Opaque secp_group_points secp_curve_group.
Lemma secp_generator_powers_complete point:In point secp_generator_powers.
Proof.
 assert (EqualLength:length secp_group_points=length secp_generator_powers).
 { apply Nat2Z.inj;rewrite <-secp_group_order_points,secp_curve_group_order_checked,
   secp_generator_powers_order;reflexivity. }
 assert (Back:incl secp_group_points secp_generator_powers).
 { apply (@List.NoDup_length_incl secp_group_point secp_generator_powers secp_group_points).
   - exact secp_generator_powers_nodup.
   - exact (eq_ind _ (fun k => (length secp_group_points <= k)%nat) (Nat.le_refl _) _ EqualLength).
   - exact secp_generator_powers_incl. }
 exact (Back point (secp_group_points_complete point)).
Qed.
Theorem secp_group_generator_spans (point:secp_group_point):
 exists k:Z,0<=k<canonical_group_order /\
 point=EGroup.gpow secp_group_generator secp_curve_group k.
Proof.
 pose proof (EGroup.support_gpow secp_group_point (SMain.ceqb secp_group_theory)
  secp_group_add secp_group_generator secp_curve_group
  (secp_group_points_complete secp_group_generator) point) as Powers.
 fold secp_generator_powers in Powers.
 destruct (Powers (secp_generator_powers_complete point)) as [k [Range Value]].
 exists k;split;[|exact Value].
 change (0<=k<Z.of_nat (length secp_generator_powers)) in Range.
 rewrite secp_generator_powers_order in Range;exact Range.
Qed.

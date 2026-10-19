(** Integer identity for libsecp256k1's magnitude-1 field negation.
    The C body stores 4*mask_i - limb_i. This file does not execute Clight. *)
From Coq Require Import ZArith Lia List.
Require Import C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Lemma fe_mask_value :
  fe_val (2 ^ 52 - feR) (2 ^ 52 - 1) (2 ^ 52 - 1) (2 ^ 52 - 1) (2 ^ 48 - 1) = feP.
Proof. vm_compute. reflexivity. Qed.

Lemma fe_negate_unreduced z0 z1 z2 z3 z4 :
  fe_val (4 * (2 ^ 52 - feR) - z0) (4 * (2 ^ 52 - 1) - z1) (4 * (2 ^ 52 - 1) - z2)
         (4 * (2 ^ 52 - 1) - z3) (4 * (2 ^ 48 - 1) - z4) =
    4 * feP - fe_val z0 z1 z2 z3 z4.
Proof.
  rewrite <- fe_mask_value. unfold fe_val. ring.
Qed.

Lemma fe_negate_limb_bounds z0 z1 z2 z3 z4 :
  fe_limbs_ok z0 z1 z2 z3 z4 ->
  0 <= 4 * (2 ^ 52 - feR) - z0 <= 2 ^ 60 /\
  0 <= 4 * (2 ^ 52 - 1) - z1 <= 2 ^ 60 /\
  0 <= 4 * (2 ^ 52 - 1) - z2 <= 2 ^ 60 /\
  0 <= 4 * (2 ^ 52 - 1) - z3 <= 2 ^ 60 /\
  0 <= 4 * (2 ^ 48 - 1) - z4 <= 2 ^ 60.
Proof.
  unfold fe_limbs_ok, feR.
  change (2 ^ 52) with 4503599627370496.
  change (2 ^ 48) with 281474976710656.
  change (2 ^ 60) with 1152921504606846976.
  intros H. lia.
Qed.

Lemma fe_negate_mod z0 z1 z2 z3 z4 :
  0 <= fe_val z0 z1 z2 z3 z4 < feP ->
  fe_val (4 * (2 ^ 52 - feR) - z0) (4 * (2 ^ 52 - 1) - z1) (4 * (2 ^ 52 - 1) - z2)
         (4 * (2 ^ 52 - 1) - z3) (4 * (2 ^ 48 - 1) - z4) mod feP =
    (feP - fe_val z0 z1 z2 z3 z4) mod feP.
Proof.
  intros Hx. rewrite fe_negate_unreduced.
  replace (4 * feP - fe_val z0 z1 z2 z3 z4) with
    (- fe_val z0 z1 z2 z3 z4 + 4 * feP) by ring.
  replace (feP - fe_val z0 z1 z2 z3 z4) with
    (- fe_val z0 z1 z2 z3 z4 + 1 * feP) by ring.
  rewrite !Z.mod_add by (unfold feP, feR; lia). reflexivity.
Qed.

Definition fe_negate_limbs (z0 z1 z2 z3 z4 : Z) : list Z :=
  match nvz (4 * (2 ^ 52 - feR) - z0) (4 * (2 ^ 52 - 1) - z1) (4 * (2 ^ 52 - 1) - z2)
            (4 * (2 ^ 52 - 1) - z3) (4 * (2 ^ 48 - 1) - z4) with
  | (r0, r1, r2, r3, r4) => [r0; r1; r2; r3; r4]
  end.

Lemma fe_negate_normalized_limbs z0 z1 z2 z3 z4 :
  fe_limbs_ok z0 z1 z2 z3 z4 ->
  fe_val z0 z1 z2 z3 z4 < feP ->
  fe_negate_limbs z0 z1 z2 z3 z4 =
    fe_limbs_of ((feP - fe_val z0 z1 z2 z3 z4) mod feP).
Proof.
  intros Hok Hlt.
  pose proof (fe_val_bound _ _ _ _ _ Hok) as Hrange.
  destruct (fe_negate_limb_bounds _ _ _ _ _ Hok) as [B0 [B1 [B2 [B3 B4]]]].
  pose proof (nvz_spec (4 * (2 ^ 52 - feR) - z0) (4 * (2 ^ 52 - 1) - z1)
    (4 * (2 ^ 52 - 1) - z2) (4 * (2 ^ 52 - 1) - z3) (4 * (2 ^ 48 - 1) - z4)
    B0 B1 B2 B3 B4) as Hspec.
  unfold fe_negate_limbs.
  destruct (nvz (4 * (2 ^ 52 - feR) - z0) (4 * (2 ^ 52 - 1) - z1)
                (4 * (2 ^ 52 - 1) - z2) (4 * (2 ^ 52 - 1) - z3)
                (4 * (2 ^ 48 - 1) - z4)) as [[[[r0 r1] r2] r3] r4].
  destruct Hspec as [Hout Hmod].
  apply fe_limbs_unique; [exact Hout|].
  rewrite Hmod. apply fe_negate_mod. lia.
Qed.

Lemma fe_negate_of_canonical_value (V : Z) :
  0 <= V < feP ->
  fe_negate_limbs (V mod 2 ^ 52) ((V / 2 ^ 52) mod 2 ^ 52) ((V / 2 ^ 104) mod 2 ^ 52)
                ((V / 2 ^ 156) mod 2 ^ 52) (V / 2 ^ 208) =
    fe_limbs_of ((feP - V) mod feP).
Proof.
  intros HV.
  assert (H256 : 0 <= V < 2 ^ 256).
  { unfold feP, feR in HV. lia. }
  destruct (fe_limbs_of_ok V H256) as [Hok Hval].
  assert (Hlt : fe_val (V mod 2 ^ 52) ((V / 2 ^ 52) mod 2 ^ 52)
    ((V / 2 ^ 104) mod 2 ^ 52) ((V / 2 ^ 156) mod 2 ^ 52)
    (V / 2 ^ 208) < feP) by (rewrite Hval; exact (proj2 HV)).
  pose proof (fe_negate_normalized_limbs _ _ _ _ _ Hok Hlt) as H.
  rewrite Hval in H. exact H.
Qed.
Print Assumptions fe_negate_of_canonical_value.

Require Import C.jet_secp_fe_nv C.jet_secp_field_negate_values.
From compcert Require Import Integers.

Lemma fe_negate_machine_normalized (rho : nat -> int64) :
  fe_limbs_ok (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) ->
  fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) < feP ->
  nvz_list (Int64.unsigned (negate_value rho 0))
    (Int64.unsigned (negate_value rho 1)) (Int64.unsigned (negate_value rho 2))
    (Int64.unsigned (negate_value rho 3)) (Int64.unsigned (negate_value rho 4)) =
  fe_limbs_of ((feP - fe_val (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat))) mod feP).
Proof.
  intros Hok Hlt.
  assert (Hbounds := Hok). unfold fe_limbs_ok in Hbounds.
  rewrite (negate_value_unsigned rho 0 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 1 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 2 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 3 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 4 ltac:(lia) ltac:(cbn; lia)).
  match goal with |- _ = ?rhs =>
  change (fe_negate_limbs (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) = rhs)
  end.
  apply fe_negate_normalized_limbs; assumption.
Qed.
Print Assumptions fe_negate_machine_normalized.

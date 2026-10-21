(** Bit-accumulator meaning in the original zero-mod-field helper. *)
From Coq Require Import ZArith List Lia Bool.
Require Import C.jet_sx_zval C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition curve_zero_test a b c d e : bool :=
  Z.eqb (Z.lor (Z.lor (Z.lor (Z.lor a b) c) d) e) 0 ||
  Z.eqb (Z.land (Z.land (Z.land (Z.land (Z.lxor a 4294968272) b) c) d)
    (Z.lxor e 4222124650659840)) 4503599627370495.

Lemma curve_xor_cancel a mask : Z.lxor (Z.lxor a mask) mask = a.
Proof. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity. Qed.

Lemma curve_xor_iff a mask target : Z.lxor a mask = target <-> a = Z.lxor target mask.
Proof.
  split; intro H.
  - rewrite <- (curve_xor_cancel a mask), H. reflexivity.
  - rewrite H, curve_xor_cancel. reflexivity.
Qed.

Lemma curve_zero_test_cases a b c d e :
  0 <= a <= 4503599627370495 -> 0 <= b <= 4503599627370495 ->
  0 <= c <= 4503599627370495 -> 0 <= d <= 4503599627370495 ->
  0 <= e <= 281474976711167 ->
  curve_zero_test a b c d e = true <->
    (a=0 /\ b=0 /\ c=0 /\ d=0 /\ e=0) \/
    (a=4503595332402223 /\ b=4503599627370495 /\ c=4503599627370495 /\
      d=4503599627370495 /\ e=281474976710655).
Proof.
  intros HA HB HC HD HE.
  assert (HX : 0 <= Z.lxor a 4294968272 <= 4503599627370495).
  { pose proof (lxor_range a 4294968272 4503599627370495 HA ltac:(lia)) as H.
    change (2 ^ (Z.log2 4503599627370495 + 1) - 1) with 4503599627370495 in H. exact H. }
  assert (HY : 0 <= Z.lxor e 4222124650659840 <= 4503599627370495).
  { pose proof (lxor_range e 4222124650659840 4503599627370495 ltac:(lia) ltac:(lia)) as H.
    change (2 ^ (Z.log2 4503599627370495 + 1) - 1) with 4503599627370495 in H. exact H. }
  assert (Hland : forall x y, 0 <= x <= 4503599627370495 -> 0 <= y <= 4503599627370495 ->
    0 <= Z.land x y <= 4503599627370495).
  { intros x y HX' HY'. split; [apply Z.land_nonneg; lia|].
    pose proof (land_le_l x y ltac:(change (2^64) with 18446744073709551616; lia)
      ltac:(change (2^64) with 18446744073709551616; lia)); lia. }
  unfold curve_zero_test. rewrite Bool.orb_true_iff, !Z.eqb_eq, !Z.lor_eq_0_iff.
  rewrite (land_eq_M52 _ _ (Hland _ _ (Hland _ _ (Hland _ _ HX HB) HC) HD) HY).
  rewrite (land_eq_M52 _ _ (Hland _ _ (Hland _ _ HX HB) HC) HD).
  rewrite (land_eq_M52 _ _ (Hland _ _ HX HB) HC).
  rewrite (land_eq_M52 _ _ HX HB).
  rewrite !curve_xor_iff.
  change (Z.lxor 4503599627370495 4294968272) with 4503595332402223.
  change (Z.lxor 4503599627370495 4222124650659840) with 281474976710655.
  tauto.
Qed.

Lemma curve_pass_value_zero_cases a b c d e :
  0 <= a <= 4503599627370495 -> 0 <= b <= 4503599627370495 ->
  0 <= c <= 4503599627370495 -> 0 <= d <= 4503599627370495 ->
  0 <= e <= 281474976711167 ->
  fe_val a b c d e mod feP = 0 <->
    (a=0 /\ b=0 /\ c=0 /\ d=0 /\ e=0) \/
    (a=4503595332402223 /\ b=4503599627370495 /\ c=4503599627370495 /\
      d=4503599627370495 /\ e=281474976710655).
Proof.
  intros HA HB HC HD HE.
  assert (HV : 0 <= fe_val a b c d e < 2*feP) by (unfold fe_val, feP, feR; lia).
  split.
  - intro HMod.
    pose proof (Z.div_mod (fe_val a b c d e) feP ltac:(unfold feP, feR; lia)) as HDiv.
    assert (HQ : 0 <= fe_val a b c d e / feP < 2).
    { split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; unfold feP, feR in *; lia. }
    assert (HCases : fe_val a b c d e = 0 \/ fe_val a b c d e = feP).
    { assert (HQCases : fe_val a b c d e / feP = 0 \/ fe_val a b c d e / feP = 1) by lia.
      destruct HQCases as [HQ0|HQ1]; rewrite HMod, ?HQ0, ?HQ1 in HDiv; lia. }
    destruct HCases as [HZ|HP].
    + left. unfold fe_val in HZ. lia.
    + right.
      assert (HL : fe_limbs_ok a b c d e).
      { unfold fe_limbs_ok. repeat split; try tauto; unfold fe_val, feP, feR in HP; lia. }
      pose proof (fe_limbs_unique a b c d e feP HL HP) as HList.
      change (fe_limbs_of feP) with
        [4503595332402223;4503599627370495;4503599627370495;4503599627370495;281474976710655] in HList.
      inversion HList. tauto.
  - intros [(-> & -> & -> & -> & ->)|(-> & -> & -> & -> & ->)]; reflexivity.
Qed.

Lemma curve_zero_test_numeric a b c d e :
  0 <= a <= 4503599627370495 -> 0 <= b <= 4503599627370495 ->
  0 <= c <= 4503599627370495 -> 0 <= d <= 4503599627370495 ->
  0 <= e <= 281474976711167 ->
  curve_zero_test a b c d e = Z.eqb (fe_val a b c d e mod feP) 0.
Proof.
  intros HA HB HC HD HE. apply Bool.eq_true_iff_eq. rewrite Z.eqb_eq.
  rewrite (curve_zero_test_cases _ _ _ _ _ HA HB HC HD HE).
  symmetry. apply curve_pass_value_zero_cases; assumption.
Qed.

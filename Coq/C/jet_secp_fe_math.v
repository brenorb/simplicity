(** Integer model of the 5x52-limb field representation of libsecp256k1 and
    of [secp256k1_fe_normalize_var]. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_sx_zval.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Definition feR : Z := 4294968273.
Definition feP : Z := 2 ^ 256 - feR.
Notation M52 := 4503599627370495 (only parsing).
Notation M48 := 281474976710655 (only parsing).

Definition fe_val (t0 t1 t2 t3 t4 : Z) : Z :=
  t0 + t1 * 2 ^ 52 + t2 * 2 ^ 104 + t3 * 2 ^ 156 + t4 * 2 ^ 208.

(** Limbs in canonical position (not necessarily below the modulus). *)
Definition fe_limbs_ok (t0 t1 t2 t3 t4 : Z) : Prop :=
  0 <= t0 <= M52 /\ 0 <= t1 <= M52 /\ 0 <= t2 <= M52 /\ 0 <= t3 <= M52 /\ 0 <= t4 <= M48.

Lemma land_ones_mod a k : 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof.
  intros Hk. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones. exact Hk.
Qed.

Lemma land_M52 a : Z.land a M52 = a mod 2 ^ 52.
Proof. exact (land_ones_mod a 52 ltac:(lia)). Qed.
Lemma land_M48 a : Z.land a M48 = a mod 2 ^ 48.
Proof. exact (land_ones_mod a 48 ltac:(lia)). Qed.

Lemma land_le_l a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z.land a b <= a.
Proof.
  change (2 ^ 64) with 18446744073709551616. intros Ha Hb.
  pose proof (Int64.and_le (Int64.repr a) (Int64.repr b)) as H.
  unfold Int64.and in H.
  rewrite !(Int64.unsigned_repr a), !(Int64.unsigned_repr b) in H
    by (change Int64.max_unsigned with 18446744073709551615; lia).
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  destruct (Z_le_dec (Z.land a b) a) as [?|N]; [assumption|].
  exfalso.
  assert (Z.land a b < 2 ^ 64).
  { destruct (Z.eq_dec (Z.land a b) 0) as [->|Hne]; [reflexivity|].
    apply Z.log2_lt_pow2; [lia|].
    pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)).
    assert (Z.log2 a < 64).
    { apply Z.log2_lt_pow2; [|change (2^64) with 18446744073709551616; lia].
      destruct (Z.eq_dec a 0); [subst; rewrite Z.land_0_l in Hne; congruence|lia]. }
    lia. }
  change (2 ^ 64) with 18446744073709551616 in *.
  rewrite Int64.unsigned_repr in H by (change Int64.max_unsigned with 18446744073709551615; lia). lia.
Qed.

Lemma land_eq_M52 a b : 0 <= a <= M52 -> 0 <= b <= M52 -> (Z.land a b = M52 <-> a = M52 /\ b = M52).
Proof.
  intros Ha Hb. split.
  - intros H. pose proof (land_le_l a b ltac:(change (2^64) with 18446744073709551616; lia) ltac:(change (2^64) with 18446744073709551616; lia)).
    pose proof (land_le_l b a ltac:(change (2^64) with 18446744073709551616; lia) ltac:(change (2^64) with 18446744073709551616; lia)).
    rewrite Z.land_comm in H1. lia.
  - intros [-> ->]. reflexivity.
Qed.

(** One carry step preserves the value. *)
Lemma carry_step a b k : 0 < k -> a mod k + (b + a / k) * k = a + b * k.
Proof. intros Hk. pose proof (Z.div_mod a k ltac:(lia)). nia. Qed.

Definition nv_pass (t0 t1 t2 t3 t4 : Z) : Z * Z * Z * Z * Z :=
  let t1a := t1 + t0 / 2 ^ 52 in
  let t0b := Z.land t0 M52 in
  let t2a := t2 + t1a / 2 ^ 52 in
  let t1b := Z.land t1a M52 in
  let t3a := t3 + t2a / 2 ^ 52 in
  let t2b := Z.land t2a M52 in
  let t4b := t4 + t3a / 2 ^ 52 in
  let t3b := Z.land t3a M52 in
  (t0b, t1b, t2b, t3b, t4b).

Lemma nv_pass_spec t0 t1 t2 t3 t4 :
  0 <= t0 -> 0 <= t1 -> 0 <= t2 -> 0 <= t3 -> 0 <= t4 ->
  match nv_pass t0 t1 t2 t3 t4 with
  | (r0, r1, r2, r3, r4) =>
      fe_val r0 r1 r2 r3 r4 = fe_val t0 t1 t2 t3 t4 /\
      0 <= r0 <= M52 /\ 0 <= r1 <= M52 /\ 0 <= r2 <= M52 /\ 0 <= r3 <= M52 /\
      t4 <= r4 /\ r4 = t4 + (t3 + (t2 + (t1 + t0 / 2 ^ 52) / 2 ^ 52) / 2 ^ 52) / 2 ^ 52
  end.
Proof.
  intros H0 H1 H2 H3 H4. unfold nv_pass, fe_val. rewrite !land_M52.
  set (t1a := t1 + t0 / 2 ^ 52). set (t2a := t2 + t1a / 2 ^ 52). set (t3a := t3 + t2a / 2 ^ 52).
  assert (0 <= t0 / 2 ^ 52) by (apply Z.div_pos; lia).
  assert (0 <= t1a / 2 ^ 52) by (apply Z.div_pos; lia).
  assert (0 <= t2a / 2 ^ 52) by (apply Z.div_pos; lia).
  assert (0 <= t3a / 2 ^ 52) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound t0 (2 ^ 52) ltac:(lia)).
  pose proof (Z.mod_pos_bound t1a (2 ^ 52) ltac:(lia)).
  pose proof (Z.mod_pos_bound t2a (2 ^ 52) ltac:(lia)).
  pose proof (Z.mod_pos_bound t3a (2 ^ 52) ltac:(lia)).
  change (2 ^ 52) with 4503599627370496 in *.
  split; [|repeat split; lia].
  pose proof (Z.div_mod t0 4503599627370496 ltac:(lia)).
  pose proof (Z.div_mod t1a 4503599627370496 ltac:(lia)).
  pose proof (Z.div_mod t2a 4503599627370496 ltac:(lia)).
  pose proof (Z.div_mod t3a 4503599627370496 ltac:(lia)).
  change (2 ^ 104) with (4503599627370496 * 4503599627370496).
  change (2 ^ 156) with (4503599627370496 * 4503599627370496 * 4503599627370496).
  change (2 ^ 208) with (4503599627370496 * 4503599627370496 * 4503599627370496 * 4503599627370496).
  unfold t3a, t2a, t1a in *. lia.
Qed.

Definition nvz (t0 t1 t2 t3 t4 : Z) : Z * Z * Z * Z * Z :=
  let x := t4 / 2 ^ 48 in
  let t4a := Z.land t4 M48 in
  let t0a := t0 + x * feR in
  match nv_pass t0a t1 t2 t3 t4a with
  | (t0b, t1b, t2b, t3b, t4b) =>
      let m := Z.land (Z.land t1b t2b) t3b in
      let x2 := Z.lor (t4b / 2 ^ 48)
                  (Z.land (Z.land (b2z (Z.eqb t4b M48)) (b2z (Z.eqb m M52)))
                          (b2z (negb (Z.ltb t0b 4503595332402223)))) in
      if negb (Z.eqb (b2z (negb (Z.eqb x2 0))) 0) then
        match nv_pass (t0b + feR) t1b t2b t3b t4b with
        | (r0, r1, r2, r3, r4) => (r0, r1, r2, r3, Z.land r4 M48)
        end
      else (t0b, t1b, t2b, t3b, t4b)
  end.

Lemma fe_val_ge_P r0 r1 r2 r3 r4 :
  fe_limbs_ok r0 r1 r2 r3 r4 ->
  (feP <= fe_val r0 r1 r2 r3 r4 <->
   r4 = M48 /\ r3 = M52 /\ r2 = M52 /\ r1 = M52 /\ 4503595332402223 <= r0).
Proof.
  unfold fe_limbs_ok, fe_val, feP, feR.
  change (2 ^ 256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
  change (2 ^ 52) with 4503599627370496.
  change (2 ^ 104) with 20282409603651670423947251286016.
  change (2 ^ 156) with 91343852333181432387730302044767688728495783936.
  change (2 ^ 208) with 411376139330301510538742295639337626245683966408394965837152256.
  intros H. lia.
Qed.

Lemma fe_val_bound r0 r1 r2 r3 r4 :
  fe_limbs_ok r0 r1 r2 r3 r4 -> 0 <= fe_val r0 r1 r2 r3 r4 < 2 ^ 256.
Proof.
  unfold fe_limbs_ok, fe_val.
  change (2 ^ 256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
  change (2 ^ 52) with 4503599627370496.
  change (2 ^ 104) with 20282409603651670423947251286016.
  change (2 ^ 156) with 91343852333181432387730302044767688728495783936.
  change (2 ^ 208) with 411376139330301510538742295639337626245683966408394965837152256.
  intros H. lia.
Qed.

Lemma mod_feP_unique V k r : V = r + k * feP -> 0 <= r < feP -> V mod feP = r.
Proof.
  intros -> Hr. rewrite Z.mod_add by (unfold feP, feR; lia). apply Z.mod_small. exact Hr.
Qed.

Lemma bool_x2 q B1 B2 B3 :
  (q = 0 \/ q = 1) ->
  (Z.lor q (Z.land (Z.land (b2z B1) (b2z B2)) (b2z B3)) = 0 <-> q = 0 /\ (B1 && B2 && B3) = false).
Proof. intros [->| ->]; destruct B1, B2, B3; simpl; split; intros; try lia; intuition congruence. Qed.

Theorem nvz_spec t0 t1 t2 t3 t4 :
  0 <= t0 <= 2 ^ 60 -> 0 <= t1 <= 2 ^ 60 -> 0 <= t2 <= 2 ^ 60 -> 0 <= t3 <= 2 ^ 60 -> 0 <= t4 <= 2 ^ 60 ->
  match nvz t0 t1 t2 t3 t4 with
  | (r0, r1, r2, r3, r4) =>
      fe_limbs_ok r0 r1 r2 r3 r4 /\
      fe_val r0 r1 r2 r3 r4 = fe_val t0 t1 t2 t3 t4 mod feP
  end.
Proof.
  intros H0 H1 H2 H3 H4. unfold nvz.
  set (x := t4 / 2 ^ 48). set (t4a := Z.land t4 M48). set (t0a := t0 + x * feR).
  assert (Hx : 0 <= x <= 4096).
  { unfold x. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|].
    change (2 ^ 60) with 1152921504606846976 in H4. change (2 ^ 48) with 281474976710656. lia. }
  assert (Ht4a : t4a = t4 mod 2 ^ 48) by (apply land_M48).
  pose proof (Z.mod_pos_bound t4 (2 ^ 48) ltac:(lia)) as Hm4.
  pose proof (Z.div_mod t4 (2 ^ 48) ltac:(lia)) as Hd4. fold x in Hd4. rewrite <- Ht4a in Hd4, Hm4.
  assert (Ht0a : 0 <= t0a <= 2 ^ 61) by (unfold t0a, feR; change (2^60) with 1152921504606846976 in H0; change (2^61) with 2305843009213693952; lia).
  pose proof (nv_pass_spec t0a t1 t2 t3 t4a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hp1.
  destruct (nv_pass t0a t1 t2 t3 t4a) as [[[[t0b t1b] t2b] t3b] t4b].
  destruct Hp1 as (Hv1 & Hb0 & Hb1 & Hb2 & Hb3 & Hge4 & He4).
  assert (Hc : t4b <= t4a + 512).
  { rewrite He4. clear He4 Hv1 Hd4.
    change (2 ^ 52) with 4503599627370496 in *. change (2 ^ 60) with 1152921504606846976 in *.
    change (2 ^ 61) with 2305843009213693952 in *.
    assert (t0a / 4503599627370496 <= 512) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= t0a / 4503599627370496) by (apply Z.div_pos; lia).
    assert ((t1 + t0a / 4503599627370496) / 4503599627370496 <= 512) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= (t1 + t0a / 4503599627370496) / 4503599627370496) by (apply Z.div_pos; lia).
    assert ((t2 + (t1 + t0a / 4503599627370496) / 4503599627370496) / 4503599627370496 <= 512) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= (t2 + (t1 + t0a / 4503599627370496) / 4503599627370496) / 4503599627370496) by (apply Z.div_pos; lia).
    assert ((t3 + (t2 + (t1 + t0a / 4503599627370496) / 4503599627370496) / 4503599627370496) / 4503599627370496 <= 512) by (apply Z.div_le_upper_bound; lia).
    lia. }
  set (V := fe_val t0 t1 t2 t3 t4) in *.
  set (V1 := fe_val t0b t1b t2b t3b t4b) in *.
  assert (HV1 : V = V1 + x * feP).
  { rewrite Hv1. unfold V, fe_val, t0a, feP.
    change (2 ^ 256) with (2 ^ 48 * 2 ^ 208). rewrite Hd4 at 1. ring. }
  set (q := t4b / 2 ^ 48).
  assert (Hq : q = 0 \/ q = 1).
  { unfold q. change (2 ^ 48) with 281474976710656 in *.
    assert (0 <= t4b / 281474976710656) by (apply Z.div_pos; lia).
    assert (t4b / 281474976710656 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (Z.div_mod t4b (2 ^ 48) ltac:(lia)) as Hdq. fold q in Hdq.
  pose proof (Z.mod_pos_bound t4b (2 ^ 48) ltac:(lia)) as Hmq.
  set (m := Z.land (Z.land t1b t2b) t3b).
  assert (Hm : m = M52 <-> t1b = M52 /\ t2b = M52 /\ t3b = M52).
  { unfold m.
    assert (0 <= Z.land t1b t2b <= M52).
    { split; [apply Z.land_nonneg; lia|].
      pose proof (land_le_l t1b t2b ltac:(change (2^64) with 18446744073709551616; lia) ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    rewrite (land_eq_M52 _ _ H Hb3). rewrite (land_eq_M52 _ _ Hb1 Hb2). tauto. }
  set (B1 := Z.eqb t4b M48). set (B2 := Z.eqb m M52). set (B3 := negb (Z.ltb t0b 4503595332402223)).
  pose proof (bool_x2 q B1 B2 B3 Hq) as Hx2.
  fold q. fold (b2z B1). fold (b2z B2). fold (b2z B3).
  destruct (Z.eqb_spec (Z.lor q (Z.land (Z.land (b2z B1) (b2z B2)) (b2z B3))) 0) as [E|N]; cbn [negb b2z Z.eqb].
  - (* no final reduction *)
    apply Hx2 in E. destruct E as [Eq EB].
    assert (Hl : fe_limbs_ok t0b t1b t2b t3b t4b).
    { unfold fe_limbs_ok. change (2^48) with 281474976710656 in *. repeat split; lia. }
    split; [exact Hl|]. fold V1.
    symmetry. apply (mod_feP_unique V x V1 HV1).
    pose proof (fe_val_bound _ _ _ _ _ Hl) as Hbd. fold V1 in Hbd. split; [lia|].
    destruct (Z_lt_dec V1 feP) as [?|Hge]; [assumption|]. exfalso.
    assert (Hge' : feP <= V1) by lia. unfold V1 in Hge'.
    apply (fe_val_ge_P _ _ _ _ _ Hl) in Hge'. destruct Hge' as (E4 & E3 & E2 & E1 & E0).
    assert (B1 = true) by (unfold B1; apply Z.eqb_eq; exact E4).
    assert (B2 = true) by (unfold B2; apply Z.eqb_eq; apply Hm; auto).
    assert (B3 = true) by (unfold B3; destruct (Z.ltb_spec t0b 4503595332402223); [lia|reflexivity]).
    subst B1 B2 B3. rewrite H, H5, H6 in EB. discriminate.
  - (* final reduction *)
    assert (Hcase : q = 1 \/ (q = 0 /\ t4b = M48 /\ t1b = M52 /\ t2b = M52 /\ t3b = M52 /\ 4503595332402223 <= t0b)).
    { destruct Hq as [Hq0|Hq1]; [|left; exact Hq1]. right. split; [exact Hq0|].
      assert (B1 && B2 && B3 = true).
      { destruct (B1 && B2 && B3) eqn:EB; [reflexivity|]. exfalso. apply N. apply Hx2. auto. }
      apply andb_true_iff in H. destruct H as [H HB3]. apply andb_true_iff in H. destruct H as [HB1 HB2].
      unfold B1 in HB1. apply Z.eqb_eq in HB1. unfold B2 in HB2. apply Z.eqb_eq in HB2.
      apply Hm in HB2. unfold B3 in HB3. destruct (Z.ltb_spec t0b 4503595332402223); [discriminate|].
      tauto. }
    pose proof (nv_pass_spec (t0b + feR) t1b t2b t3b t4b ltac:(unfold feR; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hp2.
    destruct (nv_pass (t0b + feR) t1b t2b t3b t4b) as [[[[r0 r1] r2] r3] r4'].
    destruct Hp2 as (Hv2 & Hr0 & Hr1 & Hr2 & Hr3 & Hge5 & He5).
    assert (Hc2 : r4' <= t4b + 1).
    { rewrite He5. clear He5 Hv2 HV1 Hv1 He4. unfold feR in *. change (2 ^ 52) with 4503599627370496.
      assert ((t0b + 4294968273) / 4503599627370496 < 2) by (apply Z.div_lt_upper_bound; lia).
      assert (0 <= (t0b + 4294968273) / 4503599627370496) by (apply Z.div_pos; lia).
      assert ((t1b + (t0b + 4294968273) / 4503599627370496) / 4503599627370496 < 2) by (apply Z.div_lt_upper_bound; lia).
      assert (0 <= (t1b + (t0b + 4294968273) / 4503599627370496) / 4503599627370496) by (apply Z.div_pos; lia).
      assert ((t2b + (t1b + (t0b + 4294968273) / 4503599627370496) / 4503599627370496) / 4503599627370496 < 2) by (apply Z.div_lt_upper_bound; lia).
      assert (0 <= (t2b + (t1b + (t0b + 4294968273) / 4503599627370496) / 4503599627370496) / 4503599627370496) by (apply Z.div_pos; lia).
      assert ((t3b + (t2b + (t1b + (t0b + 4294968273) / 4503599627370496) / 4503599627370496) / 4503599627370496) / 4503599627370496 < 2) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    assert (Hv2' : fe_val r0 r1 r2 r3 r4' = V1 + feR).
    { rewrite Hv2. unfold V1, fe_val. ring. }
    rewrite land_M48.
    pose proof (Z.div_mod r4' (2 ^ 48) ltac:(lia)) as Hd5.
    pose proof (Z.mod_pos_bound r4' (2 ^ 48) ltac:(lia)) as Hm5.
    assert (Hlim : fe_limbs_ok r0 r1 r2 r3 (r4' mod 2 ^ 48)).
    { unfold fe_limbs_ok. change (2^48) with 281474976710656 in *. repeat split; lia. }
    split; [exact Hlim|].
    assert (Hq5 : r4' / 2 ^ 48 = 1).
    { assert (r4' / 2 ^ 48 < 2).
      { apply Z.div_lt_upper_bound; [lia|]. change (2^48) with 281474976710656 in *. lia. }
      assert (1 <= r4' / 2 ^ 48); [|lia].
      apply Z.div_le_lower_bound; [lia|].
      destruct Hcase as [Hq1|(Hq0 & E4 & E1 & E2 & E3 & E0)].
      - rewrite Hq1 in Hdq. lia.
      - (* value reaches 2^256 *)
        destruct (Z_le_dec (2 ^ 48 * 1) r4') as [?|Hlt]; [assumption|]. exfalso.
        assert (Hl' : fe_limbs_ok r0 r1 r2 r3 r4').
        { unfold fe_limbs_ok. change (2^48) with 281474976710656 in *. repeat split; lia. }
        pose proof (fe_val_bound _ _ _ _ _ Hl') as Hbd. rewrite Hv2' in Hbd.
        assert (feP <= V1).
        { unfold V1. apply fe_val_ge_P; [|auto].
          unfold fe_limbs_ok. repeat split; try lia. }
        unfold feP in H5. lia. }
    assert (Hres : fe_val r0 r1 r2 r3 (r4' mod 2 ^ 48) = V1 - feP).
    { assert (fe_val r0 r1 r2 r3 (r4' mod 2 ^ 48) = fe_val r0 r1 r2 r3 r4' - 2 ^ 256).
      { unfold fe_val. change (2 ^ 256) with (2 ^ 48 * 2 ^ 208).
        rewrite Hd5 at 2. rewrite Hq5. ring. }
      rewrite H, Hv2'. unfold feP. ring. }
    rewrite Hres. symmetry. apply (mod_feP_unique V (x + 1) (V1 - feP)); [rewrite HV1; ring|].
    pose proof (fe_val_bound _ _ _ _ _ Hlim) as Hbd. rewrite Hres in Hbd. split; [lia|].
    (* V1 < 2 * feP *)
    assert (V1 < 2 * feP); [|lia].
    unfold V1, fe_val, feP, feR in *.
    change (2 ^ 256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936 in *.
    change (2 ^ 52) with 4503599627370496 in *.
    change (2 ^ 104) with 20282409603651670423947251286016 in *.
    change (2 ^ 156) with 91343852333181432387730302044767688728495783936 in *.
    change (2 ^ 208) with 411376139330301510538742295639337626245683966408394965837152256 in *.
    change (2 ^ 48) with 281474976710656 in *.
    lia.
Qed.

(** ** Canonical limbs of a 256-bit value *)
Definition fe_limbs_of (V : Z) : list Z :=
  [V mod 2 ^ 52; (V / 2 ^ 52) mod 2 ^ 52; (V / 2 ^ 104) mod 2 ^ 52; (V / 2 ^ 156) mod 2 ^ 52; V / 2 ^ 208].

Lemma fe_limbs_unique l0 l1 l2 l3 l4 V :
  fe_limbs_ok l0 l1 l2 l3 l4 -> fe_val l0 l1 l2 l3 l4 = V -> [l0; l1; l2; l3; l4] = fe_limbs_of V.
Proof.
  unfold fe_limbs_ok, fe_val, fe_limbs_of. intros H <-.
  change (2 ^ 104) with (2 ^ 52 * 2 ^ 52). change (2 ^ 156) with (2 ^ 52 * 2 ^ 52 * 2 ^ 52).
  change (2 ^ 208) with (2 ^ 52 * 2 ^ 52 * 2 ^ 52 * 2 ^ 52).
  assert (E1 : l0 + l1 * 2 ^ 52 + l2 * (2 ^ 52 * 2 ^ 52) + l3 * (2 ^ 52 * 2 ^ 52 * 2 ^ 52) +
               l4 * (2 ^ 52 * 2 ^ 52 * 2 ^ 52 * 2 ^ 52) =
               l0 + (l1 + (l2 + (l3 + l4 * 2 ^ 52) * 2 ^ 52) * 2 ^ 52) * 2 ^ 52) by ring.
  rewrite E1. clear E1.
  set (A1 := l1 + (l2 + (l3 + l4 * 2 ^ 52) * 2 ^ 52) * 2 ^ 52).
  assert (H0 : (l0 + A1 * 2 ^ 52) mod 2 ^ 52 = l0).
  { rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 52) with 4503599627370496. lia. }
  assert (D0 : (l0 + A1 * 2 ^ 52) / 2 ^ 52 = A1).
  { rewrite Z.div_add by lia. rewrite Z.div_small by (change (2 ^ 52) with 4503599627370496; lia). lia. }
  rewrite H0, D0.
  rewrite <- !Z.div_div by lia. rewrite D0.
  unfold A1. set (A2 := l2 + (l3 + l4 * 2 ^ 52) * 2 ^ 52).
  assert (H1 : (l1 + A2 * 2 ^ 52) mod 2 ^ 52 = l1).
  { rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 52) with 4503599627370496. lia. }
  assert (D1 : (l1 + A2 * 2 ^ 52) / 2 ^ 52 = A2).
  { rewrite Z.div_add by lia. rewrite Z.div_small by (change (2 ^ 52) with 4503599627370496; lia). lia. }
  rewrite H1, D1.
  unfold A2. set (A3 := l3 + l4 * 2 ^ 52).
  assert (H2 : (l2 + A3 * 2 ^ 52) mod 2 ^ 52 = l2).
  { rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 52) with 4503599627370496. lia. }
  assert (D2 : (l2 + A3 * 2 ^ 52) / 2 ^ 52 = A3).
  { rewrite Z.div_add by lia. rewrite Z.div_small by (change (2 ^ 52) with 4503599627370496; lia). lia. }
  rewrite H2, D2. unfold A3.
  assert (H3 : (l3 + l4 * 2 ^ 52) mod 2 ^ 52 = l3).
  { rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 52) with 4503599627370496. lia. }
  assert (D3 : (l3 + l4 * 2 ^ 52) / 2 ^ 52 = l4).
  { rewrite Z.div_add by lia. rewrite Z.div_small by (change (2 ^ 52) with 4503599627370496; lia). lia. }
  rewrite H3, D3. reflexivity.
Qed.

Lemma fe_limbs_of_ok V :
  0 <= V < 2 ^ 256 ->
  fe_limbs_ok (V mod 2 ^ 52) ((V / 2 ^ 52) mod 2 ^ 52) ((V / 2 ^ 104) mod 2 ^ 52)
              ((V / 2 ^ 156) mod 2 ^ 52) (V / 2 ^ 208) /\
  fe_val (V mod 2 ^ 52) ((V / 2 ^ 52) mod 2 ^ 52) ((V / 2 ^ 104) mod 2 ^ 52)
         ((V / 2 ^ 156) mod 2 ^ 52) (V / 2 ^ 208) = V.
Proof.
  intros HV. unfold fe_limbs_ok, fe_val.
  pose proof (Z.mod_pos_bound V (2 ^ 52) ltac:(lia)).
  pose proof (Z.mod_pos_bound (V / 2 ^ 52) (2 ^ 52) ltac:(lia)).
  pose proof (Z.mod_pos_bound (V / 2 ^ 104) (2 ^ 52) ltac:(lia)).
  pose proof (Z.mod_pos_bound (V / 2 ^ 156) (2 ^ 52) ltac:(lia)).
  assert (0 <= V / 2 ^ 208 < 2 ^ 48).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 208 * 2 ^ 48) with (2 ^ 256). lia. }
  split.
  { change (2 ^ 52) with 4503599627370496 in *. change (2 ^ 48) with 281474976710656 in *. lia. }
  pose proof (Z.div_mod V (2 ^ 52) ltac:(lia)) as E0.
  pose proof (Z.div_mod (V / 2 ^ 52) (2 ^ 52) ltac:(lia)) as E1.
  pose proof (Z.div_mod (V / 2 ^ 104) (2 ^ 52) ltac:(lia)) as E2.
  pose proof (Z.div_mod (V / 2 ^ 156) (2 ^ 52) ltac:(lia)) as E3.
  rewrite Z.div_div in E1, E2, E3 by lia.
  change (2 ^ 52 * 2 ^ 52) with (2 ^ 104) in E1. change (2 ^ 104 * 2 ^ 52) with (2 ^ 156) in E2.
  change (2 ^ 156 * 2 ^ 52) with (2 ^ 208) in E3.
  change (2 ^ 104) with (2 ^ 52 * 2 ^ 52) at 2. change (2 ^ 156) with (2 ^ 52 * 2 ^ 52 * 2 ^ 52) at 2.
  change (2 ^ 208) with (2 ^ 52 * 2 ^ 52 * 2 ^ 52 * 2 ^ 52) at 2.
  set (a0 := V mod 2 ^ 52) in *. set (a1 := (V / 2 ^ 52) mod 2 ^ 52) in *.
  set (a2 := (V / 2 ^ 104) mod 2 ^ 52) in *. set (a3 := (V / 2 ^ 156) mod 2 ^ 52) in *.
  set (q1 := V / 2 ^ 52) in *. set (q2 := V / 2 ^ 104) in *. set (q3 := V / 2 ^ 156) in *.
  set (q4 := V / 2 ^ 208) in *. lia.
Qed.

(** ** Bit-field facts for the byte conversions *)
Lemma lor_shift_add x y k : 0 <= x < 2 ^ k -> 0 <= y -> 0 <= k -> Z.lor x (y * 2 ^ k) = x + y * 2 ^ k.
Proof.
  intros Hx Hy Hk.
  assert (HL : Z.land x (y * 2 ^ k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec i k).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - destruct (Z.eq_dec x 0) as [->|Hne]; [rewrite Z.bits_0; reflexivity|].
      rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
      assert (Z.log2 x < k) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma mod_div_mod x a b c :
  0 <= b -> 0 <= c -> b + c <= a -> ((x mod 2 ^ a) / 2 ^ b) mod 2 ^ c = (x / 2 ^ b) mod 2 ^ c.
Proof.
  intros Hb Hc Ha.
  pose proof (Z.div_mod x (2 ^ a) ltac:(apply Z.pow_nonzero; lia)) as E.
  rewrite E at 2.
  replace (2 ^ a * (x / 2 ^ a)) with ((x / 2 ^ a) * 2 ^ (a - b - c) * 2 ^ c * 2 ^ b).
  2: { rewrite <- !Z.mul_assoc, <- !Z.pow_add_r by lia. replace (a - b - c + (c + b)) with a by lia. ring. }
  rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma div_div_pow x a b : 0 <= a -> 0 <= b -> x / 2 ^ a / 2 ^ b = x / 2 ^ (a + b).
Proof.
  intros. rewrite Z.div_div; [|apply Z.pow_nonzero; lia|apply Z.pow_pos_nonneg; lia].
  rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma mod256_split x : x mod 2 ^ 8 = x mod 2 ^ 4 + (x / 2 ^ 4) mod 2 ^ 4 * 2 ^ 4.
Proof.
  pose proof (Z.div_mod x (2 ^ 4) ltac:(lia)) as E.
  pose proof (Z.div_mod (x / 2 ^ 4) (2 ^ 4) ltac:(lia)) as E2.
  pose proof (Z.mod_pos_bound x (2 ^ 4) ltac:(lia)). pose proof (Z.mod_pos_bound (x / 2 ^ 4) (2 ^ 4) ltac:(lia)).
  symmetry. apply Z.mod_unique with (q := x / 2 ^ 4 / 2 ^ 4).
  - left. change (2 ^ 8) with 256. change (2 ^ 4) with 16 in *. lia.
  - change (2 ^ 8) with (2 ^ 4 * 2 ^ 4). lia.
Qed.

Lemma land_15 a : Z.land a 15 = a mod 2 ^ 4.
Proof. exact (land_ones_mod a 4 ltac:(lia)). Qed.
Lemma land_255 a : Z.land a 255 = a mod 2 ^ 8.
Proof. exact (land_ones_mod a 8 ltac:(lia)). Qed.

Lemma overflow_flag l0 l1 l2 l3 l4 :
  fe_limbs_ok l0 l1 l2 l3 l4 ->
  Z.eqb (Z.land (Z.land (b2z (Z.eqb l4 M48)) (b2z (Z.eqb (Z.land (Z.land l3 l2) l1) M52)))
                (b2z (negb (Z.ltb l0 4503595332402223)))) 0 =
  Z.ltb (fe_val l0 l1 l2 l3 l4) feP.
Proof.
  intros Hl. pose proof (fe_val_ge_P _ _ _ _ _ Hl) as HP.
  destruct Hl as (H0 & H1 & H2 & H3 & H4).
  assert (Hm : Z.land (Z.land l3 l2) l1 = M52 <-> l3 = M52 /\ l2 = M52 /\ l1 = M52).
  { assert (0 <= Z.land l3 l2 <= M52).
    { split; [apply Z.land_nonneg; lia|].
      pose proof (land_le_l l3 l2 ltac:(change (2^64) with 18446744073709551616; lia) ltac:(change (2^64) with 18446744073709551616; lia)). lia. }
    rewrite (land_eq_M52 _ _ H H1). rewrite (land_eq_M52 _ _ H3 H2). tauto. }
  destruct (Z.ltb_spec (fe_val l0 l1 l2 l3 l4) feP) as [Hlt|Hge].
  - destruct (Z.eqb_spec l4 M48) as [E4|N4]; [|reflexivity].
    destruct (Z.eqb_spec (Z.land (Z.land l3 l2) l1) M52) as [Em|Nm]; [|reflexivity].
    destruct (Z.ltb_spec l0 4503595332402223) as [E0|N0]; [reflexivity|].
    exfalso. apply Hm in Em. assert (feP <= fe_val l0 l1 l2 l3 l4) by (apply HP; tauto). lia.
  - apply HP in Hge. destruct Hge as (E4 & E3 & E2 & E1 & E0).
    assert (Em : Z.land (Z.land l3 l2) l1 = M52) by (apply Hm; tauto).
    rewrite E4, Em. destruct (Z.ltb_spec l0 4503595332402223); [lia|reflexivity].
Qed.

Definition be_val (bs : list Z) : Z := fold_left (fun acc b => acc * 256 + b) bs 0.

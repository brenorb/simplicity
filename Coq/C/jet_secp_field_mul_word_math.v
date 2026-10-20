(** Integer correctness of the original [secp256k1_fe_mul_inner] dataflow.

    The hypotheses are the 128-bit accumulator updates of the original C
    (field_5x52_int128_impl.h), one per helper call, written as integers:
    [W] is the full 128-bit value after a call, its low word is [W mod 2^64].
    No bound on an intermediate value is assumed; all are derived from the
    actual C operand limb bounds (56 bits, with a 52-bit top limb).
    Adapted from the archived independent helper proof; the canonical field
    representation predicate and the selected public jet proofs are unchanged. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_fe_math.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition feMulR : Z := 68719492368.
Lemma feMulR_feR : feMulR = 16 * feR.
Proof. reflexivity. Qed.

Lemma prod_bound x y X Y : 0 <= x <= X -> 0 <= y <= Y -> 0 <= x * y <= X * Y.
Proof. intros. split; [lia|apply Z.mul_le_mono_nonneg; lia]. Qed.

Lemma mod_small_eq a n : 0 <= a < n -> a mod n = a.
Proof. apply Z.mod_small. Qed.

Lemma fm_mod_mod_pow a k n : 0 <= k <= n -> (a mod 2 ^ n) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros Hk. replace (2 ^ n) with (2 ^ k * 2 ^ (n - k)).
  - rewrite Z.rem_mul_r by lia.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
  - rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Ltac zlin := repeat match goal with
  | H : context [Z.modulo _ _] |- _ => clear H
  | H : context [Z.div _ _] |- _ => clear H
  end; lia.

(** Actual C operand limits, including loose results of earlier field calls.
    This is a new proof predicate; the canonical fe_limbs_ok is unchanged. *)
Definition field_mul_operand_ok (t0 t1 t2 t3 t4 : Z) : Prop :=
  0 <= t0 <= 2 ^ 56 - 1 /\ 0 <= t1 <= 2 ^ 56 - 1 /\
  0 <= t2 <= 2 ^ 56 - 1 /\ 0 <= t3 <= 2 ^ 56 - 1 /\ 0 <= t4 <= 2 ^ 52 - 1.

Definition fe_mul_bound_BB : Z := (2 ^ 56 - 1) * (2 ^ 56 - 1).
Definition fe_mul_bound_BT : Z := (2 ^ 56 - 1) * (2 ^ 52 - 1).
Definition fe_mul_bound_TT : Z := (2 ^ 52 - 1) * (2 ^ 52 - 1).

Lemma land_low52 W : 0 <= W -> Z.land (W mod 2 ^ 64) (2 ^ 52 - 1) = W mod 2 ^ 52.
Proof. intros. rewrite land_ones_mod by lia. apply fm_mod_mod_pow. lia. Qed.

Lemma lo_split W : 0 <= W ->
  exists q m, W = 2 ^ 64 * q + m /\ 0 <= m < 2 ^ 64 /\ W mod 2 ^ 64 = m /\ W / 2 ^ 64 = q.
Proof.
  intros HW. exists (W / 2 ^ 64), (W mod 2 ^ 64).
  split; [apply Z.div_mod; lia|]. split; [apply Z.mod_pos_bound; lia|]. auto.
Qed.
Lemma l52_split W : 0 <= W ->
  exists q m, W = 2 ^ 52 * q + m /\ 0 <= m < 2 ^ 52 /\ W mod 2 ^ 52 = m /\ W / 2 ^ 52 = q.
Proof.
  intros HW. exists (W / 2 ^ 52), (W mod 2 ^ 52).
  split; [apply Z.div_mod; lia|]. split; [apply Z.mod_pos_bound; lia|]. auto.
Qed.

(** The column/carry dataflow on product atoms. *)
Lemma fe_mul_core
    (p00 p01 p02 p03 p04 p10 p11 p12 p13 p14 p20 p21 p22 p23 p24
     p30 p31 p32 p33 p34 p40 p41 p42 p43 p44 : Z)
    (W10 W12 W14 W16 W18 W20 W22 W24 W26 W28 W30 W32 W34 W36 W38
     W40 W42 W44 W46 W48 W50 W52 W54 W56 W58 W60 W62 W64 W66 W68 W70 W72 W74 W76
     W78 W80 W82 W84 W86 W88 W90 W92 : Z) :
  0 <= p00 <= fe_mul_bound_BB -> 0 <= p01 <= fe_mul_bound_BB -> 0 <= p02 <= fe_mul_bound_BB ->
  0 <= p03 <= fe_mul_bound_BB -> 0 <= p04 <= fe_mul_bound_BT ->
  0 <= p10 <= fe_mul_bound_BB -> 0 <= p11 <= fe_mul_bound_BB -> 0 <= p12 <= fe_mul_bound_BB ->
  0 <= p13 <= fe_mul_bound_BB -> 0 <= p14 <= fe_mul_bound_BT ->
  0 <= p20 <= fe_mul_bound_BB -> 0 <= p21 <= fe_mul_bound_BB -> 0 <= p22 <= fe_mul_bound_BB ->
  0 <= p23 <= fe_mul_bound_BB -> 0 <= p24 <= fe_mul_bound_BT ->
  0 <= p30 <= fe_mul_bound_BB -> 0 <= p31 <= fe_mul_bound_BB -> 0 <= p32 <= fe_mul_bound_BB ->
  0 <= p33 <= fe_mul_bound_BB -> 0 <= p34 <= fe_mul_bound_BT ->
  0 <= p40 <= fe_mul_bound_BT -> 0 <= p41 <= fe_mul_bound_BT -> 0 <= p42 <= fe_mul_bound_BT ->
  0 <= p43 <= fe_mul_bound_BT -> 0 <= p44 <= fe_mul_bound_TT ->
  W10 = p03 ->
  W12 = (W10 + p12) mod 2 ^ 128 -> W14 = (W12 + p21) mod 2 ^ 128 ->
  W16 = (W14 + p30) mod 2 ^ 128 -> W18 = p44 ->
  W20 = (W16 + feMulR * (W18 mod 2 ^ 64)) mod 2 ^ 128 -> W22 = W18 / 2 ^ 64 ->
  W24 = W20 / 2 ^ 52 ->
  W26 = (W24 + p04) mod 2 ^ 128 -> W28 = (W26 + p13) mod 2 ^ 128 ->
  W30 = (W28 + p22) mod 2 ^ 128 -> W32 = (W30 + p31) mod 2 ^ 128 ->
  W34 = (W32 + p40) mod 2 ^ 128 ->
  W36 = (W34 + feMulR * 2 ^ 12 * (W22 mod 2 ^ 64)) mod 2 ^ 128 -> W38 = W36 / 2 ^ 52 ->
  W40 = p00 ->
  W42 = (W38 + p14) mod 2 ^ 128 -> W44 = (W42 + p23) mod 2 ^ 128 ->
  W46 = (W44 + p32) mod 2 ^ 128 -> W48 = (W46 + p41) mod 2 ^ 128 ->
  W50 = W48 / 2 ^ 52 ->
  W52 = (W40 + Z.lor ((Z.land (W48 mod 2 ^ 64) M52 * 2 ^ 4) mod 2 ^ 64)
    (Z.land (W36 mod 2 ^ 64) M52 / 2 ^ 48) * feR) mod 2 ^ 128 ->
  W54 = W52 / 2 ^ 52 ->
  W56 = (W54 + p01) mod 2 ^ 128 -> W58 = (W56 + p10) mod 2 ^ 128 ->
  W60 = (W50 + p24) mod 2 ^ 128 -> W62 = (W60 + p33) mod 2 ^ 128 ->
  W64 = (W62 + p42) mod 2 ^ 128 ->
  W66 = (W58 + Z.land (W64 mod 2 ^ 64) M52 * feMulR) mod 2 ^ 128 ->
  W68 = W64 / 2 ^ 52 -> W70 = W66 / 2 ^ 52 ->
  W72 = (W70 + p02) mod 2 ^ 128 -> W74 = (W72 + p11) mod 2 ^ 128 ->
  W76 = (W74 + p20) mod 2 ^ 128 ->
  W78 = (W68 + p34) mod 2 ^ 128 -> W80 = (W78 + p43) mod 2 ^ 128 ->
  W82 = (W76 + feMulR * (W80 mod 2 ^ 64)) mod 2 ^ 128 -> W84 = W80 / 2 ^ 64 ->
  W86 = W82 / 2 ^ 52 ->
  W88 = (W86 + feMulR * 2 ^ 12 * (W84 mod 2 ^ 64)) mod 2 ^ 128 ->
  W90 = (W88 + Z.land (W20 mod 2 ^ 64) M52) mod 2 ^ 128 ->
  W92 = W90 / 2 ^ 52 ->
  let r0 := Z.land (W52 mod 2 ^ 64) M52 in
  let r1 := Z.land (W66 mod 2 ^ 64) M52 in
  let r2 := Z.land (W82 mod 2 ^ 64) M52 in
  let r3 := Z.land (W90 mod 2 ^ 64) M52 in
  let r4 := (W92 mod 2 ^ 64 + Z.land (Z.land (W36 mod 2 ^ 64) M52) (M52 / 2 ^ 4)) mod 2 ^ 64 in
  0 <= r0 <= M52 /\ 0 <= r1 <= M52 /\ 0 <= r2 <= M52 /\ 0 <= r3 <= M52 /\ 0 <= r4 < 2 ^ 49 /\
  exists K, fe_val r0 r1 r2 r3 r4 + K * feP =
    p00 + (p01 + p10) * 2 ^ 52 + (p02 + p11 + p20) * 2 ^ 104 +
    (p03 + p12 + p21 + p30) * 2 ^ 156 + (p04 + p13 + p22 + p31 + p40) * 2 ^ 208 +
    (p14 + p23 + p32 + p41) * 2 ^ 260 + (p24 + p33 + p42) * 2 ^ 312 +
    (p34 + p43) * 2 ^ 364 + p44 * 2 ^ 416.
Proof.
  unfold fe_mul_bound_BB, fe_mul_bound_BT, fe_mul_bound_TT.
  intros P00 P01 P02 P03 P04 P10 P11 P12 P13 P14 P20 P21 P22 P23 P24
    P30 P31 P32 P33 P34 P40 P41 P42 P43 P44
    E10 E12 E14 E16 E18 E20 E22 E24 E26 E28 E30 E32 E34 E36 E38 E40 E42 E44 E46 E48
    E50 E52 E54 E56 E58 E60 E62 E64 E66 E68 E70 E72 E74 E76 E78 E80 E82 E84 E86
    E88 E90 E92.
  assert (HR : feMulR = 68719492368) by reflexivity.
  assert (HfR : feR = 4294968273) by reflexivity.
  change M52 with (2 ^ 52 - 1) in *.
  rewrite HR in *. rewrite HfR in *.
  Ltac acc E := rewrite Z.mod_small in E; [|zlin].
  acc E12. acc E14. acc E16.
  destruct (lo_split W18 ltac:(zlin)) as (q18 & m18 & D18 & B18 & M18 & Q18).
  rewrite M18 in E20. rewrite Q18 in E22. subst W22.
  acc E20.
  rewrite (Z.mod_small q18) in E36 by zlin.
  destruct (l52_split W20 ltac:(zlin)) as (q20 & m20 & D20 & B20 & M20 & Q20).
  rewrite Q20 in E24. subst W24.
  acc E26. acc E28. acc E30. acc E32. acc E34. acc E36.
  destruct (l52_split W36 ltac:(zlin)) as (q36 & m36 & D36 & B36 & M36 & Q36).
  rewrite Q36 in E38. subst W38.
  acc E42. acc E44. acc E46. acc E48.
  destruct (l52_split W48 ltac:(zlin)) as (q48 & m48 & D48 & B48 & M48' & Q48).
  rewrite Q48 in E50. subst W50.
  rewrite (land_low52 W48), (land_low52 W36) in E52 by zlin.
  rewrite M48', M36 in E52.
  pose proof (Z.div_mod m36 (2 ^ 48) ltac:(lia)) as D4.
  pose proof (Z.mod_pos_bound m36 (2 ^ 48) ltac:(lia)) as B4.
  remember (m36 / 2 ^ 48) as tx eqn:Etx.
  remember (m36 mod 2 ^ 48) as t4 eqn:Et4.
  assert (Btx : 0 <= tx < 2 ^ 4) by (rewrite Etx; split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (m48 * 2 ^ 4)) in E52 by lia.
  assert (HU : Z.lor (m48 * 2 ^ 4) tx = tx + m48 * 2 ^ 4).
  { rewrite Z.lor_comm. apply lor_shift_add; lia. }
  rewrite HU in E52. clear HU.
  acc E52.
  destruct (l52_split W52 ltac:(zlin)) as (q52 & m52 & D52 & B52 & M52' & Q52).
  rewrite Q52 in E54. subst W54.
  acc E56. acc E58. acc E60. acc E62. acc E64.
  rewrite (land_low52 W64) in E66 by zlin.
  destruct (l52_split W64 ltac:(zlin)) as (q64 & m64 & D64 & B64 & M64 & Q64).
  rewrite M64 in E66. rewrite Q64 in E68. subst W68.
  acc E66.
  destruct (l52_split W66 ltac:(zlin)) as (q66 & m66 & D66 & B66 & M66 & Q66).
  rewrite Q66 in E70. subst W70.
  acc E72. acc E74. acc E76. acc E78. acc E80.
  destruct (lo_split W80 ltac:(zlin)) as (q80 & m80 & D80 & B80 & M80 & Q80).
  rewrite M80 in E82. rewrite Q80 in E84. subst W84.
  acc E82.
  rewrite (Z.mod_small q80) in E88 by zlin.
  destruct (l52_split W82 ltac:(zlin)) as (q82 & m82 & D82 & B82 & M82 & Q82).
  rewrite Q82 in E86. subst W86.
  acc E88.
  rewrite (land_low52 W20) in E90 by zlin. rewrite M20 in E90.
  acc E90.
  destruct (l52_split W90 ltac:(zlin)) as (q90 & m90 & D90 & B90 & M90 & Q90).
  rewrite Q90 in E92. subst W92.
  assert (Hr0 : Z.land (W52 mod 2 ^ 64) (2 ^ 52 - 1) = m52) by (rewrite land_low52 by zlin; exact M52').
  assert (Hr1 : Z.land (W66 mod 2 ^ 64) (2 ^ 52 - 1) = m66) by (rewrite land_low52 by zlin; exact M66).
  assert (Hr2 : Z.land (W82 mod 2 ^ 64) (2 ^ 52 - 1) = m82) by (rewrite land_low52 by zlin; exact M82).
  assert (Hr3 : Z.land (W90 mod 2 ^ 64) (2 ^ 52 - 1) = m90) by (rewrite land_low52 by zlin; exact M90).
  assert (Hr4 : (q90 mod 2 ^ 64 + Z.land (Z.land (W36 mod 2 ^ 64) (2 ^ 52 - 1))
      ((2 ^ 52 - 1) / 2 ^ 4)) mod 2 ^ 64 = q90 + t4).
  { rewrite land_low52 by zlin. rewrite M36.
    change ((2 ^ 52 - 1) / 2 ^ 4) with (2 ^ 48 - 1). rewrite land_ones_mod by lia.
    rewrite <- Et4. rewrite (Z.mod_small q90) by zlin. apply Z.mod_small. zlin. }
  cbv zeta. rewrite Hr0, Hr1, Hr2, Hr3, Hr4. clear Hr0 Hr1 Hr2 Hr3 Hr4.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [zlin|].
  exists (16 * (p14 + p23 + p32 + p41 + (p24 + p33 + p42) * 2 ^ 52 +
    (p34 + p43) * 2 ^ 104 + p44 * 2 ^ 156) + 16 * q36 + tx).
  unfold fe_val, feP, feR. zlin.
Qed.
Print Assumptions fe_mul_core.

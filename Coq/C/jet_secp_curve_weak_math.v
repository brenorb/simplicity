(** Integer consequence of the actual weak-normalizer carry pass. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_field_add_initial.
Require Import C.jet_secp_fe_math C.jet_secp_curve_weak.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma curve_weak_math_spec t0 t1 t2 t3 t4 :
  0 <= t0 <= 2^60 -> 0 <= t1 <= 2^60 -> 0 <= t2 <= 2^60 ->
  0 <= t3 <= 2^60 -> 0 <= t4 <= 2^60 ->
  let '(r0,r1,r2,r3,r4) := curve_weak_math t0 t1 t2 t3 t4 in
  fe_val r0 r1 r2 r3 r4 mod feP = fe_val t0 t1 t2 t3 t4 mod feP /\
  0 <= r0 <= 4503599627370495 /\ 0 <= r1 <= 4503599627370495 /\
  0 <= r2 <= 4503599627370495 /\ 0 <= r3 <= 4503599627370495 /\
  0 <= r4 <= 281474976710912.
Proof.
  intros H0 H1 H2 H3 H4.
  assert (HQ : 0 <= t4 / 2^48 <= 4096).
  { split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia. }
  assert (HA : 0 <= t0 + t4 / 2^48 * feR <= 2^61).
  { unfold feR; lia. }
  assert (HC0 : 0 <= (t0 + t4 / 2^48 * feR) / 2^52 <= 512).
  { split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia. }
  assert (HC1 : 0 <= (t1 + (t0 + t4 / 2^48 * feR) / 2^52) / 2^52 <= 257).
  { split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia. }
  assert (HC2 : 0 <= (t2 + (t1 + (t0 + t4 / 2^48 * feR) / 2^52) / 2^52) / 2^52 <= 257).
  { split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia. }
  assert (HC3 : 0 <= (t3 + (t2 + (t1 + (t0 + t4 / 2^48 * feR) / 2^52) / 2^52) / 2^52) / 2^52 <= 257).
  { split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia. }
  pose proof (Z.mod_pos_bound t4 (2^48) ltac:(lia)) as HM4.
  pose proof (nv_pass_spec (t0 + t4 / 2^48 * feR) t1 t2 t3
    (Z.land t4 281474976710655) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite land_M48; lia)) as HS.
  unfold curve_weak_math.
  destruct (nv_pass (t0 + t4 / 2^48 * feR) t1 t2 t3
    (Z.land t4 281474976710655)) as [[[[r0 r1] r2] r3] r4].
  destruct HS as (HV & HB0 & HB1 & HB2 & HB3 & HB4 & HT4).
  split.
  - assert (HE : fe_val t0 t1 t2 t3 t4 =
      fe_val r0 r1 r2 r3 r4 + (t4 / 2^48) * feP).
    { rewrite HV, land_M48. unfold fe_val, feP, feR.
      pose proof (Z.div_mod t4 (2^48) ltac:(lia)); lia. }
    rewrite HE, Z.mod_add; [reflexivity|unfold feP, feR; lia].
  - repeat split; try tauto; rewrite land_M48 in HT4, HB4; lia.
Qed.

Theorem eval_curve_weak_numeric rho m b :
  fe_at m b 0 (field_values rho 1) -> Mem.range_perm m b 0 40 Cur Freeable ->
  (forall n, (1 <= n <= 5)%nat -> Int64.unsigned (rho n) <= 2^60) ->
  exists mf r0 r1 r2 r3 r4,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
    [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (map Int64.repr [r0;r1;r2;r3;r4]) /\
  fe_val r0 r1 r2 r3 r4 mod feP = fe_val (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) mod feP /\
  (0 <= r0 <= 4503599627370495 /\ 0 <= r1 <= 4503599627370495 /\
   0 <= r2 <= 4503599627370495 /\ 0 <= r3 <= 4503599627370495 /\
   0 <= r4 <= 281474976710912) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun b' o => ~ foot [(b,0)] (map rshape local_write_initial_regs) b' o) m mf.
Proof.
  intros HF HP HB.
  destruct (eval_curve_weak_owned rho m b HF HP HB) as (mf & HC & HV & HFree & HL).
  assert (HR : forall n, (1 <= n <= 5)%nat -> 0 <= Int64.unsigned (rho n) <= 2^60).
  { intros n HN. split; [apply Int64.unsigned_range_2|apply HB; exact HN]. }
  pose proof (curve_weak_math_spec (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat))
    (HR 1%nat ltac:(lia)) (HR 2%nat ltac:(lia)) (HR 3%nat ltac:(lia))
    (HR 4%nat ltac:(lia)) (HR 5%nat ltac:(lia))) as HS.
  unfold curve_weak_math_list in HV.
  destruct (curve_weak_math (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)))
    as [[[[r0 r1] r2] r3] r4].
  destruct HS as [HValue HBounds].
  exists mf, r0, r1, r2, r3, r4.
  split; [exact HC|]. split; [exact HV|]. split; [exact HValue|].
  split; [exact HBounds|]. split; assumption.
Qed.

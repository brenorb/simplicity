(** Original equality helper with a tight first field and loose second field.
    No normalization call is added: the actual helper performs its zero test. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_zval.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions.
Require Import C.jet_secp_curve_equal C.jet_secp_curve_zero C.jet_secp_curve_zero_math C.jet_secp_curve_weak.
Require Import C.jet_secp_field_negate_values C.jet_secp_curve_frame C.jet_secp_curve_tail_values.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_equal_loose_bounds (n : nat) : Z * Z :=
  (0, if (n<=?5)%nat then
        if Nat.eqb n 5 then 562949953421311 else 4503599627370495
      else if Nat.eqb n 10 then 4503599627370495 else 72057594037927935).

Lemma field_equal_loose_checked :
  zb field_equal_loose_bounds curve_equal_ret = Some (0,1) /\ isk KI curve_equal_ret=true /\
  zb field_equal_loose_bounds curve_equal_cond = Some (0,1) /\ isk KI curve_equal_cond=true.
Proof. repeat split;reflexivity. Qed.

Lemma field_equal_loose_diff_bounds rho :
  (forall n, fst (field_equal_loose_bounds n)<=rho n<=snd (field_equal_loose_bounds n)) ->
  forall n, (1<=n<=5)%nat -> 0<=curve_equal_diff rho n<=2^60.
Proof.
  intros HB n HN. pose proof (HB n) as HA;pose proof (HB (n+5)%nat) as HC.
  unfold field_equal_loose_bounds in HA,HC;cbn [fst snd] in HA,HC.
  unfold curve_equal_diff.
  assert (HNCase : n=1%nat \/ n=2%nat \/ n=3%nat \/ n=4%nat \/ n=5%nat) by lia.
  destruct HNCase as [-> | [-> | [-> | [-> | ->]]]];
    cbn [Nat.leb Nat.eqb Nat.add Nat.sub negate_mask] in *;lia.
Qed.

Theorem eval_field_equal_loose_numeric rho layout m :
  rep rho layout curve_equal_regs m ->
  (forall n, fst (field_equal_loose_bounds n)<=Int64.unsigned (rho n)<=snd (field_equal_loose_bounds n)) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))]
      E0 mf (Vint (if Z.eqb
        (fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
          (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) mod feP)
        (fe_val (Int64.unsigned (rho 6%nat)) (Int64.unsigned (rho 7%nat)) (Int64.unsigned (rho 8%nat))
          (Int64.unsigned (rho 9%nat)) (Int64.unsigned (rho 10%nat)) mod feP)
        then Int.one else Int.zero)) /\
    rep rho layout curve_equal_regs mf /\
    lframe (fun b pos => ~foot layout (map rshape curve_equal_regs) b pos) m mf.
Proof.
  intros HR HB.
  destruct (eval_curve_equal_symbolic rho layout m HR) as (mf & HC & HF & HL).
  destruct field_equal_loose_checked as (HRC & HRK & HCC & HCK).
  pose proof (truth_zval rho field_equal_loose_bounds (lay layout) HB curve_equal_cond 0 1 HCC HCK) as HTruth.
  destruct (den_zval_int rho field_equal_loose_bounds (lay layout) HB curve_equal_ret 0 1 HRC HRK) as [HRet _].
  rewrite curve_equal_cond_zval,curve_b2z_truth in HTruth.
  rewrite curve_equal_ret_zval in HRet.
  pose proof (field_equal_loose_diff_bounds (zrho rho) HB) as HD.
  pose proof (curve_zero_math_numeric (curve_equal_diff (zrho rho) 1%nat)
    (curve_equal_diff (zrho rho) 2%nat) (curve_equal_diff (zrho rho) 3%nat)
    (curve_equal_diff (zrho rho) 4%nat) (curve_equal_diff (zrho rho) 5%nat)
    (HD 1%nat ltac:(lia)) (HD 2%nat ltac:(lia)) (HD 3%nat ltac:(lia))
    (HD 4%nat ltac:(lia)) (HD 5%nat ltac:(lia))) as HM.
  rewrite curve_equal_diff_value,curve_mod_equal in HM.
  exists mf. split;[|split;assumption]. rewrite HTruth,HRet in HC.
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))]
    E0 mf (Vint (if Z.eqb
      (fe_val (zrho rho 1%nat) (zrho rho 2%nat) (zrho rho 3%nat) (zrho rho 4%nat) (zrho rho 5%nat) mod feP)
      (fe_val (zrho rho 6%nat) (zrho rho 7%nat) (zrho rho 8%nat) (zrho rho 9%nat) (zrho rho 10%nat) mod feP)
      then Int.one else Int.zero))).
  rewrite <- HM.
  destruct (curve_zero_fast (curve_equal_diff (zrho rho) 1%nat) (curve_equal_diff (zrho rho) 5%nat)).
  - exact HC.
  - destruct (curve_weak_math (curve_equal_diff (zrho rho) 1%nat) (curve_equal_diff (zrho rho) 2%nat)
      (curve_equal_diff (zrho rho) 3%nat) (curve_equal_diff (zrho rho) 4%nat) (curve_equal_diff (zrho rho) 5%nat))
      as [[[[a b] c] d] e]. destruct (curve_zero_test a b c d e);exact HC.
Qed.

Lemma field_equal_loose_inputs a b :
  (forall i, (i<5)%nat -> Int64.unsigned (a i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  square_input_bounds b ->
  forall n, fst (field_equal_loose_bounds n)<=Int64.unsigned (curve_equal_rho a b n)<=
    snd (field_equal_loose_bounds n).
Proof.
  intros HA HB n. split;[apply Int64.unsigned_range_2|].
  pose proof (HA 0%nat ltac:(lia));pose proof (HA 1%nat ltac:(lia));
  pose proof (HA 2%nat ltac:(lia));pose proof (HA 3%nat ltac:(lia));pose proof (HA 4%nat ltac:(lia));
  pose proof (HB 0%nat ltac:(lia));pose proof (HB 1%nat ltac:(lia));
  pose proof (HB 2%nat ltac:(lia));pose proof (HB 3%nat ltac:(lia));pose proof (HB 4%nat ltac:(lia)).
  cbn [Nat.eqb] in *.
  do 11 (destruct n as [|n];
    [cbn [curve_equal_rho field_equal_loose_bounds words5 nth app Nat.eqb Nat.leb snd];
     rewrite ?Int64.unsigned_zero;lia|]).
  destruct n;cbn [curve_equal_rho field_equal_loose_bounds words5 nth app Nat.eqb Nat.leb snd];
    rewrite Int64.unsigned_zero;lia.
Qed.

Theorem eval_field_equal_loose_owned a b m ba bb :
  ba<>bb ->
  (forall i, (i<5)%nat -> Int64.unsigned (a i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  square_input_bounds b -> fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
      [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
      (Vint (if Z.eqb (radix_value a mod feP) (radix_value b mod feP) then Int.one else Int.zero)) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    lframe (fun bx _ => bx<>ba /\ bx<>bb) m mf.
Proof.
  intros HNe BA BB HA HB HFA HFB.
  destruct (eval_field_equal_loose_numeric (curve_equal_rho a b) [(ba,0);(bb,0)] m
    (curve_equal_initial a b m ba bb HNe HA HB HFA HFB) (field_equal_loose_inputs a b BA BB))
    as (mf & HC & HR & HF).
  rewrite curve_equal_first_value,curve_equal_second_value in HC.
  destruct (rep_free_region _ _ _ _ 0 40 HR ltac:(change (0<2)%nat;lia) eq_refl) as [_ FAF].
  destruct (rep_free_region _ _ _ _ 1 40 HR ltac:(change (1<2)%nat;lia) eq_refl) as [_ FBF].
  exists mf. split;[exact HC|]. split;[exact FAF|]. split;[exact FBF|].
  exact (curve_frame_two curve_equal_regs ba bb m mf eq_refl HF).
Qed.

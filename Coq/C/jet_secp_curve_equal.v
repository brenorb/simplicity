(** Actual equality helper: its private temporary, both optimized zero-test
    branches, and equality of the two represented field values modulo P.
    This is internal support, not a complete public curve-jet theorem. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_zval C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_curve_zero.
Require Import C.jet_secp_fe_math C.jet_secp_curve_weak C.jet_secp_field_negate_values.
Require Import C.jet_secp_curve_zero_math.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_equal_regs :=
  [free_region (fe_reg (vars5 1)) 40; free_region (fe_reg (vars5 6)) 40].
Definition curve_equal_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 500
  f_secp256k1_fe_equal_var [XP 0 0; XP 1 0] curve_equal_regs [] 11.
Definition curve_equal_tree := Eval vm_compute in curve_equal_run.
Definition curve_equal_cond := Eval vm_compute in match curve_equal_tree with
  | Some (RIf c _ _) => c | _ => XIc Int.zero end.
Definition curve_equal_early := Eval vm_compute in match curve_equal_tree with
  | Some (RIf _ (RDone st _) _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition curve_equal_late := Eval vm_compute in match curve_equal_tree with
  | Some (RIf _ _ (RDone st _)) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition curve_equal_ret := Eval vm_compute in match (stemps curve_equal_late)!1%positive with
  | Some x => x | _ => XIc Int.zero end.
Lemma curve_equal_run_eq : curve_equal_run =
  Some (RIf curve_equal_cond (RDone curve_equal_early ONormal) (RDone curve_equal_late ONormal)).
Proof. reflexivity. Qed.
Lemma curve_equal_logs : leaves_log_nil
  (RIf curve_equal_cond (RDone curve_equal_early ONormal) (RDone curve_equal_late ONormal)) = true.
Proof. reflexivity. Qed.
Lemma curve_equal_early_ret : (stemps curve_equal_early)!1%positive = Some (XIc Int.zero).
Proof. reflexivity. Qed.
Lemma curve_equal_late_ret : (stemps curve_equal_late)!1%positive = Some curve_equal_ret.
Proof. reflexivity. Qed.
Lemma curve_equal_regions : sregs curve_equal_early = curve_equal_regs /\
  sregs curve_equal_late = curve_equal_regs.
Proof. split; reflexivity. Qed.

Theorem eval_curve_equal_symbolic rho layout m :
  rep rho layout curve_equal_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf
    (if truth rho (lay layout) curve_equal_cond then Vint Int.zero
     else den rho (lay layout) curve_equal_ret) /\
  rep rho layout curve_equal_regs mf /\
  lframe (fun b o => ~ foot layout (map rshape curve_equal_regs) b o) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 500 f_secp256k1_fe_equal_var
    [XP 0 0; XP 1 0] curve_equal_regs 11 _ curve_equal_run_eq curve_equal_logs rho layout m HR)
    as (mf & result & HC & HF & HRet & HS & HL).
  change (map (den rho (lay layout)) [XP 0 0; XP 1 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HC.
  rewrite !Z.add_0_r in HC.
  cbn [rsel fst] in HF, HRet.
  destruct (truth rho (lay layout) curve_equal_cond) eqn:HB;
    cbn [fst] in HF, HRet.
  - rewrite curve_equal_early_ret in HRet. subst result.
    rewrite (proj1 curve_equal_regions) in HF. exists mf. split; [exact HC|]. split; assumption.
  - rewrite curve_equal_late_ret in HRet. subst result.
    rewrite (proj2 curve_equal_regions) in HF. exists mf. split; [exact HC|]. split; assumption.
Qed.

Definition curve_equal_bounds (n : nat) : Z * Z :=
  (0, if (Nat.eqb n 5 || Nat.eqb n 10)%bool then 562949953421311 else 4503599627370495).
Definition curve_equal_diff (rho : nat -> Z) (n : nat) :=
  4 * negate_mask (n-1)%nat - rho n + rho (n+5)%nat.

Lemma curve_equal_checked : zb curve_equal_bounds curve_equal_ret = Some (0,1) /\
  isk KI curve_equal_ret = true /\ zb curve_equal_bounds curve_equal_cond = Some (0,1) /\
  isk KI curve_equal_cond = true.
Proof. repeat split; reflexivity. Qed.

Lemma curve_equal_cond_zval rho :
  zval rho curve_equal_cond = b2z (curve_zero_fast (curve_equal_diff rho 1%nat)
    (curve_equal_diff rho 5%nat)).
Proof. unfold curve_zero_fast, curve_equal_diff. rewrite <- curve_b2z_and. reflexivity. Qed.

Lemma curve_equal_ret_zval rho :
  zval rho curve_equal_ret =
    let '(a,b,c,d,e) := curve_weak_math (curve_equal_diff rho 1%nat)
      (curve_equal_diff rho 2%nat) (curve_equal_diff rho 3%nat)
      (curve_equal_diff rho 4%nat) (curve_equal_diff rho 5%nat) in b2z (curve_zero_test a b c d e).
Proof.
  unfold curve_equal_diff, curve_weak_math, nv_pass, curve_zero_test.
  rewrite <- curve_b2z_or. reflexivity.
Qed.

Lemma curve_equal_diff_bounds rho :
  (forall n, fst (curve_equal_bounds n) <= rho n <= snd (curve_equal_bounds n)) ->
  forall n, (1 <= n <= 5)%nat -> 0 <= curve_equal_diff rho n <= 2^60.
Proof.
  intros HB n HN. pose proof (HB n) as HA. pose proof (HB (n+5)%nat) as HC.
  unfold curve_equal_bounds in HA, HC; cbn [fst snd] in HA, HC.
  unfold curve_equal_diff.
  assert (HNCase : n=1%nat \/ n=2%nat \/ n=3%nat \/ n=4%nat \/ n=5%nat) by lia.
  destruct HNCase as [-> | [-> | [-> | [-> | ->]]]];
    cbn [Nat.eqb Nat.add Nat.sub negate_mask orb] in *; lia.
Qed.

Lemma curve_equal_diff_value rho :
  fe_val (curve_equal_diff rho 1%nat) (curve_equal_diff rho 2%nat)
    (curve_equal_diff rho 3%nat) (curve_equal_diff rho 4%nat) (curve_equal_diff rho 5%nat) =
  4 * feP - fe_val (rho 1%nat) (rho 2%nat) (rho 3%nat) (rho 4%nat) (rho 5%nat) +
    fe_val (rho 6%nat) (rho 7%nat) (rho 8%nat) (rho 9%nat) (rho 10%nat).
Proof.
  unfold curve_equal_diff, negate_mask, fe_val, feP, feR. cbn [Nat.add Nat.sub]. ring.
Qed.

Lemma curve_mod_equal a b :
  Z.eqb ((4*feP - a + b) mod feP) 0 = Z.eqb (a mod feP) (b mod feP).
Proof.
  replace (4*feP - a + b) with (b-a + 4*feP) by ring.
  rewrite Z.mod_add by (unfold feP, feR; lia).
  rewrite Zminus_mod.
  apply Bool.eq_true_iff_eq. rewrite !Z.eqb_eq.
  rewrite Z.mod_divide by (unfold feP, feR; lia).
  pose proof (Z.mod_pos_bound a feP ltac:(unfold feP, feR; lia)) as HA.
  pose proof (Z.mod_pos_bound b feP ltac:(unfold feP, feR; lia)) as HB.
  split.
  - intros [k HK]. unfold feP, feR in *. nia.
  - intro HE. rewrite HE. exists 0. ring.
Qed.

Theorem eval_curve_equal_numeric rho layout m :
  rep rho layout curve_equal_regs m ->
  (forall n, fst (curve_equal_bounds n) <= Int64.unsigned (rho n) <= snd (curve_equal_bounds n)) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf
    (Vint (if Z.eqb
      (fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
        (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) mod feP)
      (fe_val (Int64.unsigned (rho 6%nat)) (Int64.unsigned (rho 7%nat))
        (Int64.unsigned (rho 8%nat)) (Int64.unsigned (rho 9%nat)) (Int64.unsigned (rho 10%nat)) mod feP)
      then Int.one else Int.zero)) /\
  rep rho layout curve_equal_regs mf /\
  lframe (fun b o => ~ foot layout (map rshape curve_equal_regs) b o) m mf.
Proof.
  intros HR HB.
  destruct (eval_curve_equal_symbolic rho layout m HR) as (mf & HC & HF & HL).
  destruct curve_equal_checked as (HRC & HRK & HCC & HCK).
  pose proof (truth_zval rho curve_equal_bounds (lay layout) HB
    curve_equal_cond 0 1 HCC HCK) as HTruth.
  destruct (den_zval_int rho curve_equal_bounds (lay layout) HB
    curve_equal_ret 0 1 HRC HRK) as [HRet _].
  rewrite curve_equal_cond_zval, curve_b2z_truth in HTruth.
  rewrite curve_equal_ret_zval in HRet.
  pose proof (curve_equal_diff_bounds (zrho rho) HB) as HD.
  pose proof (curve_zero_math_numeric (curve_equal_diff (zrho rho) 1%nat)
    (curve_equal_diff (zrho rho) 2%nat) (curve_equal_diff (zrho rho) 3%nat)
    (curve_equal_diff (zrho rho) 4%nat) (curve_equal_diff (zrho rho) 5%nat)
    (HD 1%nat ltac:(lia)) (HD 2%nat ltac:(lia)) (HD 3%nat ltac:(lia))
    (HD 4%nat ltac:(lia)) (HD 5%nat ltac:(lia))) as HM.
  rewrite curve_equal_diff_value, curve_mod_equal in HM.
  exists mf. split; [|split; assumption].
  rewrite HTruth, HRet in HC.
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf
    (Vint (if Z.eqb
      (fe_val (zrho rho 1%nat) (zrho rho 2%nat) (zrho rho 3%nat) (zrho rho 4%nat) (zrho rho 5%nat) mod feP)
      (fe_val (zrho rho 6%nat) (zrho rho 7%nat) (zrho rho 8%nat) (zrho rho 9%nat) (zrho rho 10%nat) mod feP)
      then Int.one else Int.zero))).
  rewrite <- HM.
  destruct (curve_zero_fast (curve_equal_diff (zrho rho) 1%nat) (curve_equal_diff (zrho rho) 5%nat)).
  - exact HC.
  - destruct (curve_weak_math (curve_equal_diff (zrho rho) 1%nat)
      (curve_equal_diff (zrho rho) 2%nat) (curve_equal_diff (zrho rho) 3%nat)
      (curve_equal_diff (zrho rho) 4%nat) (curve_equal_diff (zrho rho) 5%nat)) as [[[[a b] c] d] e].
    destruct (curve_zero_test a b c d e); exact HC.
Qed.

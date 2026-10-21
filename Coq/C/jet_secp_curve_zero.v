(** Original variable-time zero-mod-field test, including its early return. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_zval C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_curve_weak.
Require Import C.jet_secp_fe_math C.jet_secp_curve_zero_math.
Require Import C.jet_secp_curve_weak_math.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_zero_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 300
  f_secp256k1_fe_normalizes_to_zero_var [XP 0 0] local_write_initial_regs [] 6.
Definition curve_zero_tree := Eval vm_compute in curve_zero_run.
Definition curve_zero_cond := Eval vm_compute in match curve_zero_tree with
  | Some (RIf c _ _) => c | _ => XIc Int.zero end.
Definition curve_zero_early := Eval vm_compute in match curve_zero_tree with
  | Some (RIf _ (RDone st _) _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition curve_zero_late := Eval vm_compute in match curve_zero_tree with
  | Some (RIf _ _ (RDone st _)) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition curve_zero_ret := Eval vm_compute in match (stemps curve_zero_late)!1%positive with
  | Some x => x | _ => XIc Int.zero end.
Lemma curve_zero_run_eq : curve_zero_run =
  Some (RIf curve_zero_cond (RDone curve_zero_early ONormal) (RDone curve_zero_late ONormal)).
Proof. reflexivity. Qed.
Lemma curve_zero_logs : leaves_log_nil
  (RIf curve_zero_cond (RDone curve_zero_early ONormal) (RDone curve_zero_late ONormal)) = true.
Proof. reflexivity. Qed.
Lemma curve_zero_early_ret : (stemps curve_zero_early)!1%positive = Some (XIc Int.zero).
Proof. reflexivity. Qed.
Lemma curve_zero_late_ret : (stemps curve_zero_late)!1%positive = Some curve_zero_ret.
Proof. reflexivity. Qed.
Lemma curve_zero_regions : sregs curve_zero_early = local_write_initial_regs /\
  sregs curve_zero_late = local_write_initial_regs.
Proof. split; reflexivity. Qed.
Lemma curve_zero_checked : zb curve_weak_bounds curve_zero_ret = Some (0,1) /\
  isk KI curve_zero_ret = true /\ zb curve_weak_bounds curve_zero_cond = Some (0,1) /\
  isk KI curve_zero_cond = true.
Proof. repeat split; reflexivity. Qed.

Theorem eval_curve_zero_symbolic rho layout m :
  rep rho layout local_write_initial_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
    (if truth rho (lay layout) curve_zero_cond then Vint Int.zero
     else den rho (lay layout) curve_zero_ret) /\
  rep rho layout local_write_initial_regs mf /\
  lframe (fun b o => ~ foot layout (map rshape local_write_initial_regs) b o) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 300 f_secp256k1_fe_normalizes_to_zero_var
    [XP 0 0] local_write_initial_regs 6 _ curve_zero_run_eq curve_zero_logs rho layout m HR)
    as (mf & result & HC & HF & HRet & HS & HL).
  change (map (den rho (lay layout)) [XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HC.
  rewrite Z.add_0_r in HC.
  cbn [rsel fst] in HF, HRet.
  destruct (truth rho (lay layout) curve_zero_cond) eqn:HB;
    cbn [fst] in HF, HRet.
  - rewrite curve_zero_early_ret in HRet. subst result.
    rewrite (proj1 curve_zero_regions) in HF. exists mf. split; [exact HC|]. split; assumption.
  - rewrite curve_zero_late_ret in HRet. subst result.
    rewrite (proj2 curve_zero_regions) in HF. exists mf. split; [exact HC|]. split; assumption.
Qed.

Definition curve_zero_fast t0 t4 :=
  let a := Z.land (t0 + (t4 / 2^48) * feR) 4503599627370495 in
  negb (Z.eqb a 0) && negb (Z.eqb (Z.lxor a 4294968272) 4503599627370495).

Lemma curve_b2z_and a b : Z.land (b2z a) (b2z b) = b2z (a && b).
Proof. destruct a,b; reflexivity. Qed.
Lemma curve_b2z_or a b : Z.lor (b2z a) (b2z b) = b2z (a || b).
Proof. destruct a,b; reflexivity. Qed.

Lemma curve_zero_cond_zval rho :
  zval rho curve_zero_cond = b2z (curve_zero_fast (rho 1%nat) (rho 5%nat)).
Proof. unfold curve_zero_fast. rewrite <- curve_b2z_and. reflexivity. Qed.

Lemma curve_zero_ret_zval rho :
  zval rho curve_zero_ret =
    let '(a,b,c,d,e) := curve_weak_math (rho 1%nat) (rho 2%nat)
      (rho 3%nat) (rho 4%nat) (rho 5%nat) in b2z (curve_zero_test a b c d e).
Proof.
  unfold curve_weak_math, nv_pass, curve_zero_test. rewrite <- curve_b2z_or. reflexivity.
Qed.

Lemma curve_zero_math_numeric t0 t1 t2 t3 t4 :
  0 <= t0 <= 2^60 -> 0 <= t1 <= 2^60 -> 0 <= t2 <= 2^60 ->
  0 <= t3 <= 2^60 -> 0 <= t4 <= 2^60 ->
  (if curve_zero_fast t0 t4 then false else
    let '(a,b,c,d,e) := curve_weak_math t0 t1 t2 t3 t4 in curve_zero_test a b c d e) =
    Z.eqb (fe_val t0 t1 t2 t3 t4 mod feP) 0.
Proof.
  intros H0 H1 H2 H3 H4.
  pose proof (curve_weak_math_spec _ _ _ _ _ H0 H1 H2 H3 H4) as HS.
  assert (HFirst : let '(a,b,c,d,e) := curve_weak_math t0 t1 t2 t3 t4 in
    a = Z.land (t0 + (t4 / 2^48)*feR) 4503599627370495) by reflexivity.
  destruct (curve_weak_math t0 t1 t2 t3 t4) as [[[[a b] c] d] e].
  destruct HS as (HV & HA & HB & HC & HD & HE).
  pose proof (curve_zero_test_numeric a b c d e HA HB HC HD ltac:(lia)) as HT.
  rewrite HV in HT.
  destruct (curve_zero_fast t0 t4) eqn:HF; [|exact HT].
  assert (HFalse : curve_zero_test a b c d e = false).
  { apply Bool.not_true_is_false. intro HTrue.
    apply (curve_zero_test_cases a b c d e HA HB HC HD ltac:(lia)) in HTrue.
    unfold curve_zero_fast in HF. rewrite <- HFirst in HF.
    destruct HTrue as [(HA0 & _)|(HAP & _)];
      [rewrite HA0 in HF|rewrite HAP in HF]; discriminate. }
  rewrite <- HT, HFalse. reflexivity.
Qed.

Lemma curve_b2z_truth b : negb (Z.eqb (b2z b) 0) = b.
Proof. destruct b; reflexivity. Qed.

Theorem eval_curve_zero_numeric rho layout m :
  rep rho layout local_write_initial_regs m ->
  (forall n, (1 <= n <= 5)%nat -> Int64.unsigned (rho n) <= 2^60) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
    (Vint (if Z.eqb (fe_val (Int64.unsigned (rho 1%nat))
      (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
      (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) mod feP) 0
      then Int.one else Int.zero)) /\
  rep rho layout local_write_initial_regs mf /\
  lframe (fun b o => ~ foot layout (map rshape local_write_initial_regs) b o) m mf.
Proof.
  intros HR HB.
  destruct (eval_curve_zero_symbolic rho layout m HR) as (mf & HC & HF & HL).
  pose proof (curve_weak_bounds_holds rho HB) as HBAll.
  destruct curve_zero_checked as (HRC & HRK & HCC & HCK).
  pose proof (truth_zval rho curve_weak_bounds (lay layout) HBAll
    curve_zero_cond 0 1 HCC HCK) as HTruth.
  destruct (den_zval_int rho curve_weak_bounds (lay layout) HBAll
    curve_zero_ret 0 1 HRC HRK) as [HRet _].
  rewrite curve_zero_cond_zval, curve_b2z_truth in HTruth.
  rewrite curve_zero_ret_zval in HRet.
  assert (HRange : forall n, (1 <= n <= 5)%nat -> 0 <= Int64.unsigned (rho n) <= 2^60).
  { intros n HN. split; [apply Int64.unsigned_range_2|apply HB; exact HN]. }
  pose proof (curve_zero_math_numeric (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat))
    (HRange 1%nat ltac:(lia)) (HRange 2%nat ltac:(lia)) (HRange 3%nat ltac:(lia))
    (HRange 4%nat ltac:(lia)) (HRange 5%nat ltac:(lia))) as HM.
  exists mf. split; [|split; assumption].
  rewrite HTruth, HRet in HC.
  rewrite <- HM. unfold zrho in HC.
  destruct (curve_zero_fast (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 5%nat))) eqn:HBFast.
  - exact HC.
  - destruct (curve_weak_math (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
      (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
      (Int64.unsigned (rho 5%nat))) as [[[[a b] c] d] e].
    destruct (curve_zero_test a b c d e); exact HC.
Qed.

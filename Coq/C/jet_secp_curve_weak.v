(** Actual weak normalization of a caller-owned temporary. The inputs may be
    loose multiplier outputs, including the following +7 operation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_fe_math.
Require Import C.jet_secp_field_add_initial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_weak_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  f_secp256k1_fe_normalize_weak [XP 0 0] local_write_initial_regs [] 6.
Definition curve_weak_tree := Eval vm_compute in curve_weak_run.
Definition curve_weak_state := match curve_weak_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma curve_weak_run_eq : curve_weak_run = Some (RDone curve_weak_state ONormal).
Proof. reflexivity. Qed.
Lemma curve_weak_return : (stemps curve_weak_state)!1%positive = None.
Proof. reflexivity. Qed.
Definition curve_weak_bounds (n : nat) : Z * Z :=
  (0, if (Nat.leb 1 n && Nat.leb n 5)%bool then 2^60 else Int64.max_unsigned).
Lemma curve_weak_cells_checked :
  zreg_okb curve_weak_bounds 0 (cells0 curve_weak_state) = true.
Proof. reflexivity. Qed.
Definition curve_weak_math t0 t1 t2 t3 t4 :=
  nv_pass (t0 + (t4 / 2^48)*feR) t1 t2 t3 (Z.land t4 M48).
Definition curve_weak_math_list t0 t1 t2 t3 t4 :=
  let '(r0,r1,r2,r3,r4) := curve_weak_math t0 t1 t2 t3 t4 in [r0;r1;r2;r3;r4].
Lemma curve_weak_cells_values rho :
  zcells rho (cells0 curve_weak_state) =
    curve_weak_math_list (rho 1%nat) (rho 2%nat) (rho 3%nat) (rho 4%nat) (rho 5%nat).
Proof. reflexivity. Qed.

Theorem eval_curve_weak_symbolic rho layout m :
  rep rho layout local_write_initial_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
  rep rho layout (sregs curve_weak_state) mf /\
  lframe (fun b o => ~ foot layout (map rshape local_write_initial_regs) b o) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_normalize_weak
    [XP 0 0] local_write_initial_regs 6 _ curve_weak_run_eq eq_refl rho layout m HR)
    as (mf & result & HC & HF & HRet & HS & HL).
  cbn [rsel fst] in HF, HRet. rewrite curve_weak_return in HRet. subst result.
  change (map (den rho (lay layout)) [XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HC.
  rewrite Z.add_0_r in HC. exists mf. split; [exact HC|]. split; assumption.
Qed.

Lemma curve_weak_initial_rep rho m b :
  fe_at m b 0 (field_values rho 1) -> Mem.range_perm m b 0 40 Cur Freeable ->
  rep rho [(b, 0)] local_write_initial_regs m.
Proof.
  intros HF HP. unfold local_write_initial_regs.
  apply (rep_add rho [] [] m b 0); [apply rep_nil|cbn; tauto|].
  apply region_with_freeable.
  - apply field_region_from_values. exact HF.
  - reflexivity.
  - reflexivity.
  - exact HP.
  - apply field_region_storage_size.
Qed.

Lemma curve_weak_bounds_holds rho :
  (forall n, (1 <= n <= 5)%nat -> Int64.unsigned (rho n) <= 2^60) ->
  forall n, fst (curve_weak_bounds n) <= Int64.unsigned (rho n) <= snd (curve_weak_bounds n).
Proof.
  intros HB n. unfold curve_weak_bounds; cbn [fst snd].
  pose proof (Int64.unsigned_range_2 (rho n)).
  destruct (Nat.leb 1 n && Nat.leb n 5)%bool eqn:HN; [|lia].
  apply Bool.andb_true_iff in HN. destruct HN as [HA HZ].
  apply Nat.leb_le in HA, HZ. split; [lia|apply HB; lia].
Qed.

Lemma curve_weak_final_loads rho layout m :
  (forall n, (1 <= n <= 5)%nat -> Int64.unsigned (rho n) <= 2^60) ->
  rep rho layout (sregs curve_weak_state) m ->
  forall i z, nth_error (curve_weak_math_list
    (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat))) i = Some z ->
    Mem.load Mint64 m (blk layout 0) (bas layout 0 + 8 * Z.of_nat i) =
      Some (Vlong (Int64.repr z)).
Proof.
  intros HB HR.
  pose proof (curve_weak_bounds_holds rho HB) as HBAll.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as HRegion.
  destruct HRegion as (_ & _ & _ & HC & _).
  change (Forall (cell_ok rho layout m 0 true) (cells0 curve_weak_state)) in HC.
  destruct (zreg_load rho curve_weak_bounds layout HBAll m 0 true
    (cells0 curve_weak_state) 0 curve_weak_cells_checked HC) as [HL _].
  rewrite curve_weak_cells_values in HL.
  intros i z HZ. specialize (HL i z HZ). rewrite Z.add_0_l in HL. exact HL.
Qed.

Theorem eval_curve_weak_owned rho m b :
  fe_at m b 0 (field_values rho 1) -> Mem.range_perm m b 0 40 Cur Freeable ->
  (forall n, (1 <= n <= 5)%nat -> Int64.unsigned (rho n) <= 2^60) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
    [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (map Int64.repr (curve_weak_math_list
    (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)))) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun b' o => ~ foot [(b,0)] (map rshape local_write_initial_regs) b' o) m mf.
Proof.
  intros HF HP HB.
  destruct (eval_curve_weak_symbolic rho [(b,0)] m (curve_weak_initial_rep rho m b HF HP))
    as (mf & HC & HR & HL).
  pose proof (curve_weak_final_loads rho [(b,0)] mf HB HR) as HLoads.
  destruct (rep_free_region _ _ _ _ 0 40 HR ltac:(change (0 < 1)%nat; lia) eq_refl) as [_ HFree].
  change (Mem.range_perm mf b 0 40 Cur Freeable) in HFree.
  exists mf. split; [exact HC|]. split; [|split; assumption].
  destruct HF as (H0 & HA & HM & _).
  split; [exact H0|]. split; [exact HA|]. split; [exact HM|]. split.
  - intros o HO. eapply Mem.perm_implies; [apply HFree; lia|constructor].
  - intros i x HN. rewrite nth_error_map in HN.
    destruct (nth_error _ i) as [z|] eqn:HZ; [|discriminate].
    inversion HN; subst x. exact (HLoads i z HZ).
Qed.

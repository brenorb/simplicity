(** Original weak helper in the actual 88-byte affine allocation.
    Public affine negation and canonical ownership composition remain separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_point_write_run C.jet_secp_point_weak_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive affine_coordinate := AffineX | AffineY.
Definition affine_point_coordinate k := match k with AffineX => PointX | AffineY => PointY end.
Definition affine_coordinate_offset k := point_coordinate_offset (affine_point_coordinate k).
Definition affine_initial_regs k : list region :=
  [free_region (mkreg (u64_cells (affine_coordinate_offset k) (vars5 1)) true None) 88].
Lemma affine_actual_size : sizeof (genv_cenv secp_ge) (Tstruct __6121 noattr) = 88.
Proof. reflexivity. Qed.
Definition affine_weak_run k : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160 f_secp256k1_fe_normalize_weak
    [XP 0 (affine_coordinate_offset k)] (affine_initial_regs k) [] 6.
Definition affine_weak_tree := Eval vm_compute in fun k =>
  match k with AffineX => affine_weak_run AffineX | AffineY => affine_weak_run AffineY end.
Definition affine_weak_state k : sstate :=
  match affine_weak_tree k with
  | Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0
  end.
Lemma affine_weak_run_eq k : affine_weak_run k = Some (RDone (affine_weak_state k) ONormal).
Proof. destruct k; reflexivity. Qed.
Lemma affine_weak_return k : (stemps (affine_weak_state k))!1%positive = None.
Proof. destruct k; reflexivity. Qed.
Lemma affine_weak_log_nil k : leaves_log_nil (RDone (affine_weak_state k) ONormal) = true.
Proof. destruct k; reflexivity. Qed.
Lemma affine_weak_cells_match_point k :
  map rcells (sregs (affine_weak_state k)) =
    map rcells (sregs (point_weak_state (affine_point_coordinate k))).
Proof. destruct k; reflexivity. Qed.
Lemma affine_weak_owned_size k :
  rfree (nth 0 (sregs (affine_weak_state k)) (mkreg [] true None)) = Some 88.
Proof. destruct k; reflexivity. Qed.

Theorem eval_affine_weak_from_owned_region k m layout rho :
  rep rho layout (affine_initial_regs k) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+affine_coordinate_offset k))]
      E0 mf Vundef /\
    rep rho layout (sregs (affine_weak_state k)) mf /\
    lframe (fun b pos => ~ foot layout (map rshape (affine_initial_regs k)) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_normalize_weak
    [XP 0 (affine_coordinate_offset k)] (affine_initial_regs k) 6 _
    (affine_weak_run_eq k) (affine_weak_log_nil k) rho layout m HRep)
    as (mf & result & HCall & HFinal & HReturn & HShape & HFrame).
  cbn [rsel fst] in HFinal,HReturn.
  rewrite affine_weak_return in HReturn; subst result.
  change (map (den rho (lay layout)) [XP 0 (affine_coordinate_offset k)]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+affine_coordinate_offset k))] in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_affine_weak_from_owned_region.

Theorem eval_affine_weak_retains_freeable k m layout rho :
  rep rho layout (affine_initial_regs k) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+affine_coordinate_offset k))]
      E0 mf Vundef /\
    rep rho layout (sregs (affine_weak_state k)) mf /\
    Mem.range_perm mf (blk layout 0) 0 88 Cur Freeable /\
    lframe (fun b pos => ~ foot layout (map rshape (affine_initial_regs k)) b pos) m mf.
Proof.
  intro HI.
  destruct (eval_affine_weak_from_owned_region k m layout rho HI)
    as (mf & HC & HR & HF).
  assert (HIndex : (0 < length (sregs (affine_weak_state k)))%nat).
  { destruct k; change (0 < 1)%nat; lia. }
  pose proof (proj2 (rep_free_region rho layout (sregs (affine_weak_state k)) mf
    0 88 HR HIndex (affine_weak_owned_size k))) as HP.
  exists mf; split; [exact HC|]; split; [exact HR|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_affine_weak_retains_freeable.

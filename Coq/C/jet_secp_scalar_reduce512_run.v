(** Original reduce512 execution; numeric/specification bridges are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_shift64_executor C.jet_secp_frame.
Require Import C.jet_sx_compact C.jet_secp_compact_shift64 C.jet_sx_u64_rebuild.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition scalar_reduce512_initial_regs : list region :=
  [mkreg (u64_cells 0 [XLv 8; XLv 9; XLv 10; XLv 11]) true (Some 32);
   mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3; XLv 4; XLv 5; XLv 6; XLv 7]) true (Some 64)].
Definition scalar_reduce512_run : option res :=
  compact_fun (genv_cenv secp_ge) [] secp_shift64_table 300
    f_secp256k1_scalar_reduce_512 [XP 0 0; XP 1 0] scalar_reduce512_initial_regs [] 12.
Lemma scalar_reduce512_run_completes :
  match scalar_reduce512_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition scalar_reduce512_state : sstate :=
  match scalar_reduce512_run with Some (RDone st _) => st
    | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma scalar_reduce512_run_eq : scalar_reduce512_run = Some (RDone scalar_reduce512_state ONormal).
Proof.
  pose proof scalar_reduce512_run_completes as H.
  unfold scalar_reduce512_state; destruct scalar_reduce512_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Lemma scalar_reduce512_return : (stemps scalar_reduce512_state)!1%positive = None.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma scalar_reduce512_log_shift64 : slog scalar_reduce512_state =
  repeat (mkev 0 12 0 []) 6.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition scalar_reduce512_limbs : list sx :=
  map cell_sx (rcells (hd (mkreg [] false None) (sregs scalar_reduce512_state))).
Lemma scalar_reduce512_limbs_length : length scalar_reduce512_limbs = 4%nat.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma scalar_reduce512_limbs_kind : forallb (isk KL) scalar_reduce512_limbs = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma scalar_reduce512_owned_metadata :
  length (sregs scalar_reduce512_state) = 2%nat /\
  nth_error (sregs scalar_reduce512_state) 1 =
    Some (mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3; XLv 4; XLv 5; XLv 6; XLv 7]) true (Some 64)) /\
  rw (hd (mkreg [] false None) (sregs scalar_reduce512_state)) = true /\
  rfree (hd (mkreg [] false None) (sregs scalar_reduce512_state)) = Some 32 /\
  initialized_u64_cells 0 (rcells (hd (mkreg [] false None) (sregs scalar_reduce512_state))) = true.
Proof. Timeout 10 (repeat split; vm_compute; reflexivity). Qed.
Lemma scalar_reduce512_output : sregs scalar_reduce512_state =
  [mkreg (u64_cells 0 scalar_reduce512_limbs) true (Some 32);
   mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3; XLv 4; XLv 5; XLv 6; XLv 7]) true (Some 64)].
Proof.
  destruct scalar_reduce512_owned_metadata as [Hlen [Hsrc [Hw [Hsz Hcells]]]].
  exact (two_owned_u64_rebuild _ _ _ Hlen Hsrc Hw Hsz Hcells).
Qed.

Local Opaque scalar_reduce512_state.
Theorem eval_scalar_reduce512_owned rho beta m :
  rep rho beta scalar_reduce512_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    rep rho beta
      [mkreg (u64_cells 0 scalar_reduce512_limbs) true (Some 32);
       mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3; XLv 4; XLv 5; XLv 6; XLv 7]) true (Some 64)] mf /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_reduce512_initial_regs) b ofs) m mf.
Proof.
  intro Hrep.
  destruct (compact_fun_shift64_sound 300 f_secp256k1_scalar_reduce_512 [XP 0 0; XP 1 0]
    scalar_reduce512_initial_regs 12 (RDone scalar_reduce512_state ONormal) scalar_reduce512_run_eq
    rho beta m Hrep) as (mf & vres & Hcall & Hfinal & Hreturn & Hshape & Hframe).
  cbn [rsel fst] in Hfinal,Hreturn.
  rewrite scalar_reduce512_return in Hreturn; subst vres.
  rewrite scalar_reduce512_output in Hfinal.
  change (map (den rho (lay beta)) [XP 0 0; XP 1 0]) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0))] in Hcall.
  rewrite !Z.add_0_r in Hcall.
  exists mf; split; [exact Hcall|]. split; [exact Hfinal|exact Hframe].
Qed.

Theorem eval_scalar_reduce512_owned_loads rho beta m :
  rep rho beta scalar_reduce512_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    (forall i sy, nth_error scalar_reduce512_limbs i = Some sy ->
      Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (den rho (lay beta) sy)) /\
    rep rho beta (sregs scalar_reduce512_state) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_reduce512_initial_regs) b ofs) m mf.
Proof.
  intro Hrep.
  destruct (eval_scalar_reduce512_owned rho beta m Hrep) as (mf & Hcall & Hfinal & Hframe).
  pose proof (rep_region rho beta _ mf 0 _ Hfinal eq_refl) as Hregion.
  exists mf; split; [exact Hcall|]. split.
  { intros i sy Hnth.
    pose proof (u64_cells_nth scalar_reduce512_limbs 0 i sy Hnth) as HC.
    rewrite Z.add_0_l in HC.
    exact (region_load rho beta mf 0 _ (8 * Z.of_nat i) Mint64 sy Hregion HC). }
  rewrite <- scalar_reduce512_output in Hfinal.
  split; [exact Hfinal|exact Hframe].
Qed.

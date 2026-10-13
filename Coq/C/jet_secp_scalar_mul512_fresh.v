(** Actual product helper with freshly allocated, uninitialized output.
    Matches the scalar_mul caller; no initialized output assumption. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events Globalenvs.
From compcert Require Import Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_sx_pure.
Require Import C.jet_sx_compact C.jet_secp_scalar_mul512_run
  C.jet_secp_scalar_mul512_machine C.jet_secp_scalar_mul512_symbolic
  C.jet_secp_scalar_mul512_product C.jet_secp_scalar_mul512_owned_product
  C.jet_secp_scalar_mul512_accumulate C.jet_secp_scalar_mul512_low.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_mul512_fresh_regs : list region :=
  mkreg (map (fun c => mkcell (cofs c) (cchunk c) None)
    (rcells (hd (mkreg [] false None) scalar_mul512_initial_regs))) true (Some 64) ::
  tl scalar_mul512_initial_regs.
Definition scalar_mul512_fresh_run :=
  compact_fun (genv_cenv secp_ge) [] (int_table scalar_mul512_functions) 200
    f_secp256k1_scalar_mul_512 [XP 0 0; XP 1 0; XP 2 0]
    scalar_mul512_fresh_regs [] 16.
Lemma scalar_mul512_fresh_completes :
  match scalar_mul512_fresh_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition scalar_mul512_fresh_state :=
  match scalar_mul512_fresh_run with Some (RDone st _) => st
  | _ => mkst (Maps.PTree.empty sx) [] [] 0 end.
Lemma scalar_mul512_fresh_run_eq :
  scalar_mul512_fresh_run = Some (RDone scalar_mul512_fresh_state ONormal).
Proof.
  pose proof scalar_mul512_fresh_completes as H.
  unfold scalar_mul512_fresh_state; destruct scalar_mul512_fresh_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Lemma scalar_mul512_fresh_output : sregs scalar_mul512_fresh_state = sregs scalar_mul512_state.
Proof. Timeout 10 (rewrite scalar_mul512_output; reflexivity). Qed.
Lemma scalar_mul512_fresh_return : (stemps scalar_mul512_fresh_state)!1%positive = None.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma scalar_mul512_fresh_log_nil : slog scalar_mul512_fresh_state = [].
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Local Opaque scalar_mul512_state scalar_mul512_fresh_state.
Theorem eval_scalar_mul512_fresh rho beta m :
  rep rho beta scalar_mul512_fresh_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
    rep rho beta (sregs scalar_mul512_state) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul512_fresh_regs) b ofs) m mf.
Proof.
  intro HR.
  destruct (compact_fun_pure secp_ge scalar_mul512_functions scalar_mul512_functions_ok
    200 f_secp256k1_scalar_mul_512 [XP 0 0; XP 1 0; XP 2 0] scalar_mul512_fresh_regs
    16 (RDone scalar_mul512_fresh_state ONormal) scalar_mul512_fresh_run_eq
    ltac:(cbn [leaves_log_nil]; rewrite scalar_mul512_fresh_log_nil; reflexivity) rho beta m HR)
    as (mf & vres & HC & Hrep & Hreturn & Hshape & Hframe).
  cbn [rsel fst] in Hrep,Hreturn.
  rewrite scalar_mul512_fresh_return in Hreturn; subst vres.
  rewrite scalar_mul512_fresh_output in Hrep.
  change (map (den rho (lay beta)) [XP 0 0; XP 1 0; XP 2 0]) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2 + 0))] in HC.
  rewrite !Z.add_0_r in HC.
  exists mf; exact (conj HC (conj Hrep Hframe)).
Qed.
Theorem eval_scalar_mul512_fresh_product rho beta m :
  rep rho beta scalar_mul512_fresh_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
    (forall i x, nth_error (scalar_mul512_machine_outputs rho) i = Some x ->
      Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (Vlong x)) /\
    column_words_value (scalar_mul512_machine_outputs rho) =
      scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4 /\
    rep rho beta (sregs scalar_mul512_state) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul512_fresh_regs) b ofs) m mf.
Proof.
  intro HR; destruct (eval_scalar_mul512_fresh rho beta m HR) as (mf & HC & Hrep & HF).
  pose proof Hrep as HRout; rewrite scalar_mul512_output in HRout.
  pose proof (rep_region rho beta _ mf 0 _ HRout eq_refl) as Hregion.
  exists mf; split; [exact HC|]. split.
  - intros i x HX.
    destruct (scalar_mul512_machine_cell rho (lay beta) i x HX) as (sy & Hcell & Hden).
    rewrite <- Hden; exact (region_load rho beta mf 0 _ (8 * Z.of_nat i) Mint64 sy Hregion Hcell).
  - split; [apply scalar_mul512_machine_product|exact (conj Hrep HF)].
Qed.

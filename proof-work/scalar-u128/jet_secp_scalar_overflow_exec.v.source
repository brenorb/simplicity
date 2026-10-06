(** Original scalar overflow classifier on four readable limbs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_pure.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition scalar_overflow_initial_regs :=
  [mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) false None].
Definition scalar_overflow_run :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 100 f_secp256k1_scalar_check_overflow
    [XP 0 0] scalar_overflow_initial_regs [] 4.
Definition scalar_overflow_tree := Eval vm_compute in scalar_overflow_run.
Definition scalar_overflow_state :=
  match scalar_overflow_tree with Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition scalar_overflow_return :=
  match (stemps scalar_overflow_state)!1%positive with Some x => x | None => XIc Int.zero end.
Lemma scalar_overflow_run_eq : scalar_overflow_run = Some (RDone scalar_overflow_state ONormal).
Proof. reflexivity. Qed.
Lemma scalar_overflow_return_eq :
  (stemps scalar_overflow_state)!1%positive = Some scalar_overflow_return.
Proof. reflexivity. Qed.
Lemma scalar_overflow_regions : sregs scalar_overflow_state = scalar_overflow_initial_regs.
Proof. reflexivity. Qed.
Local Opaque scalar_overflow_state.
Theorem eval_scalar_overflow_from_readable_region rho layout m :
  rep rho layout scalar_overflow_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_check_overflow)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
      (den rho (lay layout) scalar_overflow_return) /\
    rep rho layout scalar_overflow_initial_regs mf /\
    lframe (fun b ofs => ~ foot layout (map rshape scalar_overflow_initial_regs) b ofs) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 100 f_secp256k1_scalar_check_overflow
    [XP 0 0] scalar_overflow_initial_regs 4 _ scalar_overflow_run_eq eq_refl rho layout m HRep)
    as [mf [vres [HCall [HFinal [HReturn [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HReturn.
  rewrite scalar_overflow_return_eq in HReturn; subst vres.
  rewrite scalar_overflow_regions in HFinal.
  change (map (den rho (lay layout)) [XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.

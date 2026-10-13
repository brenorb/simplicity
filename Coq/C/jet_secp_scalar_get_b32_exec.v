(** Original C scalar byte/limb helpers: actual Clight calls and memory regions.
    Numeric reduction/byte encoding and the public scalar jet chain remain open. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jet_secp_fe_b32 C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition scalar_get_regs :=
  [mkreg (byte_undef 0 32) true None;
   mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) false None].
Definition scalar_get_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 400 f_secp256k1_scalar_get_b32
    [XP 0 0; XP 1 0] scalar_get_regs [] 4.
Definition scalar_get_tree := Eval vm_compute in scalar_get_run.
Definition scalar_get_state : sstate :=
  match scalar_get_tree with Some (RDone state _) => state | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma scalar_get_run_eq : scalar_get_run = Some (RDone scalar_get_state ONormal).
Proof. reflexivity. Qed.
Lemma scalar_get_return : (stemps scalar_get_state)!1%positive = None.
Proof. reflexivity. Qed.
Theorem eval_scalar_get_b32_from_initial_regions m layout rho :
  rep rho layout scalar_get_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_b32)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    rep rho layout (sregs scalar_get_state) mf /\
    lframe (fun b pos => ~ foot layout (map rshape scalar_get_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_scalar_get_b32
    [XP 0 0; XP 1 0] scalar_get_regs 4 _ scalar_get_run_eq eq_refl rho layout m HRep)
    as [mf [result [HCall [HFinal [HReturn [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HReturn.
  rewrite scalar_get_return in HReturn; subst result.
  change (map (den rho (lay layout)) [XP 0 0; XP 1 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HCall.
  rewrite !Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.

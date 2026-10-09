(** Actual original C addition of two owned field regions.
    This helper execution theorem is not a complete jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Require Import C.jet_secp_fe_nv.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_add_initial_regs :=
  [free_region (fe_reg (vars5 1)) 40; free_region (fe_reg (vars5 6)) 40].
Definition field_add_args : list sx := [XP 0 0; XP 1 0].
Definition field_add_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96 f_secp256k1_fe_add
    field_add_args field_add_initial_regs [] 11.
Definition field_add_tree := Eval vm_compute in field_add_run.
Definition field_add_state : sstate :=
  match field_add_tree with
  | Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0
  end.
Lemma field_add_run_eq : field_add_run = Some (RDone field_add_state ONormal).
Proof. reflexivity. Qed.
Lemma field_add_return : (stemps field_add_state)!1%positive = None.
Proof. reflexivity. Qed.

Theorem eval_field_add_from_owned_region m layout rho :
  rep rho layout field_add_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))]
      E0 mf Vundef /\
    rep rho layout (sregs field_add_state) mf /\
    map rshape (sregs field_add_state) = map rshape field_add_initial_regs /\
    lframe (fun b pos => ~ foot layout (map rshape field_add_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 96 f_secp256k1_fe_add
    field_add_args field_add_initial_regs 11 _ field_add_run_eq eq_refl rho layout m HRep)
    as (mf & result & HCall & HFinal & HReturn & HShape & HFrame).
  cbn [rsel fst] in HFinal, HReturn, HShape.
  rewrite field_add_return in HReturn. subst result.
  change (map (den rho (lay layout)) field_add_args) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HCall.
  rewrite !Z.add_0_r in HCall.
  exists mf. split; [exact HCall|].
  split; [exact HFinal|]. split; assumption.
Qed.
Print Assumptions eval_field_add_from_owned_region.

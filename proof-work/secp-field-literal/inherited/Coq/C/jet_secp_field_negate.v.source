(** Actual original magnitude-one C negation on an owned field region.
    This helper execution theorem is not a complete jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_negate_args : list sx := [XP 0 0; XP 0 0; XIc Int.one].
Definition field_negate_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160 f_secp256k1_fe_negate
    field_negate_args local_write_initial_regs [] 6.
Definition field_negate_tree := Eval vm_compute in field_negate_run.
Definition field_negate_state : sstate :=
  match field_negate_tree with
  | Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0
  end.
Lemma field_negate_run_eq : field_negate_run = Some (RDone field_negate_state ONormal).
Proof. reflexivity. Qed.
Lemma field_negate_return : (stemps field_negate_state)!1%positive = None.
Proof. reflexivity. Qed.

Theorem eval_field_negate_from_owned_region m layout rho :
  rep rho layout local_write_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0)); Vint Int.one]
      E0 mf Vundef /\
    rep rho layout (sregs field_negate_state) mf /\
    map rshape (sregs field_negate_state) = map rshape local_write_initial_regs /\
    lframe (fun b pos => ~ foot layout (map rshape local_write_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_negate
    field_negate_args local_write_initial_regs 6 _ field_negate_run_eq eq_refl rho layout m HRep)
    as (mf & result & HCall & HFinal & HReturn & HShape & HFrame).
  cbn [rsel fst] in HFinal, HReturn, HShape.
  rewrite field_negate_return in HReturn. subst result.
  change (map (den rho (lay layout)) field_negate_args) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0)); Vint Int.one] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf. split; [exact HCall|].
  split; [exact HFinal|]. split; assumption.
Qed.
Print Assumptions eval_field_negate_from_owned_region.

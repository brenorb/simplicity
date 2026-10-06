(** Original C scalar zero test on a represented owned four-limb region.
    Helper execution only; the public scalar jet lifecycle remains outstanding. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_sx_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition scalar_initial_regs : list region :=
  [mkreg (u64_cells 0 [XLv 1; XLv 2; XLv 3; XLv 4]) true (Some 32)].
Definition scalar_zero_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 80 f_secp256k1_scalar_is_zero
    [XP 0 0] scalar_initial_regs [] 5.
Definition scalar_zero_tree := Eval vm_compute in scalar_zero_run.
Definition scalar_zero_state : sstate :=
  match scalar_zero_tree with Some (RDone state _) => state | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition scalar_zero_ret := Eval vm_compute in
  match (stemps scalar_zero_state)!1%positive with Some x => x | None => XIc Int.zero end.
Lemma scalar_zero_run_eq : scalar_zero_run = Some (RDone scalar_zero_state ONormal).
Proof. reflexivity. Qed.
Lemma scalar_zero_return : (stemps scalar_zero_state)!1%positive = Some scalar_zero_ret.
Proof. reflexivity. Qed.
Lemma scalar_zero_regions : sregs scalar_zero_state = scalar_initial_regs.
Proof. reflexivity. Qed.

Definition scalar_or_value (rho : nat -> int64) : int64 :=
  Int64.or (Int64.or (Int64.or (rho 1%nat) (rho 2%nat)) (rho 3%nat)) (rho 4%nat).
Lemma scalar_zero_value rho layout :
  den rho layout scalar_zero_ret =
    Vint (if Int64.eq (scalar_or_value rho) Int64.zero then Int.one else Int.zero).
Proof. reflexivity. Qed.
Theorem eval_scalar_zero_from_owned_region m layout rho :
  rep rho layout scalar_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
      (Vint (if Int64.eq (scalar_or_value rho) Int64.zero then Int.one else Int.zero)) /\
    rep rho layout scalar_initial_regs mf /\
    lframe (fun b pos => ~ foot layout (map rshape scalar_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 80 f_secp256k1_scalar_is_zero
    [XP 0 0] scalar_initial_regs 5 _ scalar_zero_run_eq eq_refl rho layout m HRep)
    as [mf [result [HCall [HFinal [HReturn [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HReturn.
  rewrite scalar_zero_regions in HFinal.
  rewrite scalar_zero_return in HReturn.
  change (result = den rho (lay layout) scalar_zero_ret) in HReturn.
  rewrite scalar_zero_value in HReturn; subst result.
  change (map (den rho (lay layout)) [XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.

(** Original C zero test on a represented, owned field region. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition field_zero_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 80 f_secp256k1_fe_is_zero
    [XP 0 0] local_write_initial_regs [] 6.
Definition field_zero_tree := Eval vm_compute in field_zero_run.
Definition field_zero_state : sstate :=
  match field_zero_tree with Some (RDone state _) => state | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition field_zero_ret := Eval vm_compute in
  match (stemps field_zero_state)!1%positive with Some x => x | None => XIc Int.zero end.
Lemma field_zero_run_eq : field_zero_run = Some (RDone field_zero_state ONormal).
Proof. reflexivity. Qed.
Lemma field_zero_return : (stemps field_zero_state)!1%positive = Some field_zero_ret.
Proof. reflexivity. Qed.
Lemma field_zero_regions : sregs field_zero_state = local_write_initial_regs.
Proof. reflexivity. Qed.

Definition field_or_value (rho : nat -> int64) : int64 :=
  Int64.or (Int64.or (Int64.or (Int64.or (rho 1%nat) (rho 2%nat)) (rho 3%nat)) (rho 4%nat)) (rho 5%nat).
Lemma field_zero_value rho layout :
  den rho layout field_zero_ret =
    Vint (if Int64.eq (field_or_value rho) Int64.zero then Int.one else Int.zero).
Proof. reflexivity. Qed.
Theorem eval_field_zero_from_owned_region m layout rho :
  rep rho layout local_write_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
      (Vint (if Int64.eq (field_or_value rho) Int64.zero then Int.one else Int.zero)) /\
    rep rho layout local_write_initial_regs mf /\
    lframe (fun b pos => ~ foot layout (map rshape local_write_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 80 f_secp256k1_fe_is_zero
    [XP 0 0] local_write_initial_regs 6 _ field_zero_run_eq eq_refl rho layout m HRep)
    as [mf [result [HCall [HFinal [HReturn [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HReturn.
  rewrite field_zero_regions in HFinal.
  rewrite field_zero_return in HReturn.
  change (result = den rho (lay layout) field_zero_ret) in HReturn.
  rewrite field_zero_value in HReturn; subst result.
  change (map (den rho (lay layout)) [XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.

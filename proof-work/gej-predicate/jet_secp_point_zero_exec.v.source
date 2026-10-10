(** Original field zero-test on a coordinate of one actual owned point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_local_regions C.jet_secp_field_zero C.jet_secp_point_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_zero_run k : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 80 f_secp256k1_fe_is_zero
    [XP 0 (point_coordinate_offset k)] (point_write_initial_regs k) [] 6.
Definition point_zero_tree := Eval vm_compute in fun k =>
  match k with
  | PointX => point_zero_run PointX
  | PointY => point_zero_run PointY
  | PointZ => point_zero_run PointZ
  end.
Definition point_zero_state k : sstate :=
  match point_zero_tree k with
  | Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0
  end.
Definition point_zero_ret := Eval vm_compute in fun k =>
  match (stemps (point_zero_state k))!1%positive with
  | Some x => x | None => XIc Int.zero
  end.

Lemma point_zero_run_eq k :
  point_zero_run k = Some (RDone (point_zero_state k) ONormal).
Proof. destruct k; reflexivity. Qed.
Lemma point_zero_return k :
  (stemps (point_zero_state k))!1%positive = Some (point_zero_ret k).
Proof. destruct k; reflexivity. Qed.
Lemma point_zero_regions k :
  sregs (point_zero_state k) = point_write_initial_regs k.
Proof. destruct k; reflexivity. Qed.
Lemma point_zero_log_nil k :
  leaves_log_nil (RDone (point_zero_state k) ONormal) = true.
Proof. destruct k; reflexivity. Qed.
Lemma point_zero_value k rho layout :
  den rho layout (point_zero_ret k) =
    Vint (if Int64.eq (field_or_value rho) Int64.zero then Int.one else Int.zero).
Proof. destruct k; reflexivity. Qed.

Theorem eval_point_zero_from_owned_region k m layout rho :
  rep rho layout (point_write_initial_regs k) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + point_coordinate_offset k))]
      E0 mf (Vint (if Int64.eq (field_or_value rho) Int64.zero then Int.one else Int.zero)) /\
    rep rho layout (point_write_initial_regs k) mf /\
    lframe (fun b pos => ~ foot layout (map rshape (point_write_initial_regs k)) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 80 f_secp256k1_fe_is_zero
    [XP 0 (point_coordinate_offset k)] (point_write_initial_regs k) 6 _
    (point_zero_run_eq k) (point_zero_log_nil k) rho layout m HRep)
    as [mf [result [HCall [HFinal [HReturn [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HReturn.
  rewrite point_zero_regions in HFinal.
  rewrite point_zero_return in HReturn.
  change (result = den rho (lay layout) (point_zero_ret k)) in HReturn.
  rewrite point_zero_value in HReturn; subst result.
  change (map (den rho (lay layout)) [XP 0 (point_coordinate_offset k)]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + point_coordinate_offset k))] in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.
Print Assumptions eval_point_zero_from_owned_region.

(** Original magnitude-one field negation at a coordinate of an owned point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_point_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_negate_args k :=
  [XP 0 (point_coordinate_offset k);XP 0 (point_coordinate_offset k);XIc Int.one].
Definition point_negate_run k : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160 f_secp256k1_fe_negate
    (point_negate_args k) (point_write_initial_regs k) [] 6.
Definition point_negate_tree := Eval vm_compute in fun k =>
  match k with
  | PointX => point_negate_run PointX
  | PointY => point_negate_run PointY
  | PointZ => point_negate_run PointZ
  end.
Definition point_negate_state k : sstate :=
  match point_negate_tree k with
  | Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0
  end.
Lemma point_negate_run_eq k : point_negate_run k = Some (RDone (point_negate_state k) ONormal).
Proof. destruct k; reflexivity. Qed.
Lemma point_negate_return k : (stemps (point_negate_state k))!1%positive = None.
Proof. destruct k; reflexivity. Qed.
Lemma point_negate_log_nil k : leaves_log_nil (RDone (point_negate_state k) ONormal) = true.
Proof. destruct k; reflexivity. Qed.

Theorem eval_point_negate_from_owned_region k m layout rho :
  rep rho layout (point_write_initial_regs k) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+point_coordinate_offset k));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+point_coordinate_offset k)); Vint Int.one]
      E0 mf Vundef /\
    rep rho layout (sregs (point_negate_state k)) mf /\
    lframe (fun b pos => ~ foot layout (map rshape (point_write_initial_regs k)) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_negate
    (point_negate_args k) (point_write_initial_regs k) 6 _
    (point_negate_run_eq k) (point_negate_log_nil k) rho layout m HRep)
    as (mf & result & HCall & HFinal & HReturn & HShape & HFrame).
  cbn [rsel fst] in HFinal,HReturn.
  rewrite point_negate_return in HReturn; subst result.
  change (map (den rho (lay layout)) (point_negate_args k)) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+point_coordinate_offset k));
     Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+point_coordinate_offset k));Vint Int.one] in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_point_negate_from_owned_region.

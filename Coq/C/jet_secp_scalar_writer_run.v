(** Exact symbolic run of the unchanged original write_scalar function,
    including its actual local buffer lifecycle and write8s event. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_writer_initial_regs : list region :=
  [mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) true (Some 32)].
Definition scalar_writer_run bd base : option res :=
  xfun (genv_cenv secp_ge) [] write_fe_table 600 f_write_scalar
    [XA bd base; XP 0 0] scalar_writer_initial_regs [] 4.
Definition scalar_writer_tree := Eval vm_compute in fun bd base => scalar_writer_run bd base.
Definition scalar_writer_result bd base : res :=
  match scalar_writer_tree bd base with Some result => result
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal end.

Lemma scalar_writer_run_eq bd base :
  scalar_writer_run bd base = Some (scalar_writer_result bd base).
Proof. reflexivity. Qed.
Lemma scalar_writer_return bd base rho layout :
  (stemps (fst (rsel rho layout (scalar_writer_result bd base))))!1%positive = None.
Proof. reflexivity. Qed.
Lemma scalar_writer_regions bd base rho layout :
  sregs (fst (rsel rho layout (scalar_writer_result bd base))) = scalar_writer_initial_regs.
Proof. reflexivity. Qed.

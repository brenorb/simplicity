(** Original field writer inside the actual owned enclosing allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Memory Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_write_fe_wrapper.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_point_write_run C.jet_secp_owned_field_slice.
Require Import C.jet_secp_linkage C.jet_secp_frame C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition owned_write_initial_regs size k : list region :=
  owned_field_slice (point_coordinate_offset k) size.
Definition owned_write_run size k bd base : option res :=
  xfun (genv_cenv secp_ge) [] write_fe_table 400 f_write_fe
    [XA bd base; XP 0 (point_coordinate_offset k)] (owned_write_initial_regs size k) [] 6.
Definition owned_write_tree := Eval vm_compute in fun size k bd base =>
  match k with
  | PointX => owned_write_run size PointX bd base
  | PointY => owned_write_run size PointY bd base
  | PointZ => owned_write_run size PointZ bd base
  end.
Definition owned_write_result size k bd base : res :=
  match owned_write_tree size k bd base with
  | Some rr => rr
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal
  end.

Lemma owned_write_tree_nonempty size k bd base :
  match owned_write_tree size k bd base with Some _ => true | None => false end = true.
Proof. destruct k; reflexivity. Qed.
Lemma owned_write_run_eq size k bd base :
  owned_write_run size k bd base = Some (owned_write_result size k bd base).
Proof. destruct k; reflexivity. Qed.
Lemma owned_write_selected_return size k bd base rho layout :
  (stemps (fst (rsel rho layout (owned_write_result size k bd base))))!1%positive = None.
Proof.
  destruct k; cbn [owned_write_result owned_write_tree rsel fst stemps];
    repeat match goal with |- context[if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma owned_write_selected_log size k bd base rho layout :
  slog (fst (rsel rho layout (owned_write_result size k bd base))) =
  slog (fst (rsel rho layout (write_fe_result bd base))).
Proof. destruct k; rewrite !selected_events_rsel; reflexivity. Qed.

Definition owned_write_storage_shape size state : Prop :=
  length (sregs state) = 1%nat /\
  rfree (nth 0 (sregs state) (mkreg [] true None)) = Some size.
Lemma owned_write_leaf_storage size k bd base :
  all_leaf_property (owned_write_storage_shape size) (owned_write_result size k bd base).
Proof. destruct k; split; split; reflexivity. Qed.
Lemma owned_write_selected_storage size k bd base rho layout :
  owned_write_storage_shape size (fst (rsel rho layout (owned_write_result size k bd base))).
Proof. apply all_leaf_property_selected; apply owned_write_leaf_storage. Qed.
Lemma owned_write_field_storage_size size k :
  point_coordinate_offset k+40 <= size ->
  Forall (fun c => cofs c+size_chunk (cchunk c) <= size)
    (rcells (hd (mkreg [] true None) (owned_write_initial_regs size k))).
Proof. apply owned_field_cells_fit. Qed.

(** Original field writer using a field slice inside an owned point region.
    Ownership belongs to the whole point, never to a fictitious offset allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Memory Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_write_fe_wrapper.
Require Import C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_linkage C.jet_secp_frame C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive point_coordinate := PointX | PointY | PointZ.
Definition point_coordinate_offset k : Z :=
  match k with PointX => 0 | PointY => 40 | PointZ => 80 end.
Definition point_write_initial_regs k : list region :=
  [free_region (mkreg (u64_cells (point_coordinate_offset k) (vars5 1)) true None) 128].
Definition point_write_run k bd base : option res :=
  xfun (genv_cenv secp_ge) [] write_fe_table 400 f_write_fe
    [XA bd base; XP 0 (point_coordinate_offset k)] (point_write_initial_regs k) [] 6.
Definition point_write_tree := Eval vm_compute in fun k bd base =>
  match k with
  | PointX => point_write_run PointX bd base
  | PointY => point_write_run PointY bd base
  | PointZ => point_write_run PointZ bd base
  end.
Definition point_write_result k bd base : res :=
  match point_write_tree k bd base with
  | Some rr => rr
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal
  end.

Lemma point_coordinate_offset_bounds k : 0 <= point_coordinate_offset k <= 80.
Proof. destruct k; cbn; lia. Qed.
Lemma point_write_tree_nonempty k bd base :
  match point_write_tree k bd base with Some _ => true | None => false end = true.
Proof. destruct k; reflexivity. Qed.
Lemma point_write_run_eq k bd base :
  point_write_run k bd base = Some (point_write_result k bd base).
Proof. destruct k; reflexivity. Qed.
Lemma point_write_selected_return k bd base rho layout :
  (stemps (fst (rsel rho layout (point_write_result k bd base))))!1%positive = None.
Proof.
  destruct k; cbn [point_write_result point_write_tree rsel fst stemps];
    repeat match goal with |- context[if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma point_write_selected_log k bd base rho layout :
  slog (fst (rsel rho layout (point_write_result k bd base))) =
  slog (fst (rsel rho layout (write_fe_result bd base))).
Proof. destruct k; rewrite !selected_events_rsel; reflexivity. Qed.

Definition point_write_storage_shape state : Prop :=
  length (sregs state) = 1%nat /\
  rfree (nth 0 (sregs state) (mkreg [] true None)) = Some 128.
Lemma point_write_leaf_storage k bd base :
  all_leaf_property point_write_storage_shape (point_write_result k bd base).
Proof. destruct k; split; split; reflexivity. Qed.
Lemma point_write_selected_storage k bd base rho layout :
  point_write_storage_shape (fst (rsel rho layout (point_write_result k bd base))).
Proof. apply all_leaf_property_selected; apply point_write_leaf_storage. Qed.
Lemma point_write_field_storage_size k :
  Forall (fun c => cofs c + size_chunk (cchunk c) <= 128)
    (rcells (hd (mkreg [] true None) (point_write_initial_regs k))).
Proof. destruct k; repeat constructor; cbn; lia. Qed.

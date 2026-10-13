(** Shared original field reader inside a genuinely owned enclosing object.
    The enclosing allocation size is preserved, not replaced by a point size. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Memory Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_point_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition owned_read_initial_regs size k bi edge : list region :=
  let delta := point_coordinate_offset k in
  [free_region
     (mkreg [mkcell delta Mint64 None; mkcell (delta+8) Mint64 None;
       mkcell (delta+16) Mint64 None; mkcell (delta+24) Mint64 None;
       mkcell (delta+32) Mint64 None] true None) size;
   free_region (mkreg (mk_frame_cells (XA bi edge) Int64.zero) true None) 16].
Definition owned_read_run size k bi edge : option res :=
  xfun (genv_cenv secp_ge) [] read_fe_table 400 f_read_fe
    [XP 0 (point_coordinate_offset k); XP 1 0]
    (owned_read_initial_regs size k bi edge) [] 1.
Definition owned_read_tree := Eval vm_compute in fun size k bi edge =>
  match k with
  | PointX => owned_read_run size PointX bi edge
  | PointY => owned_read_run size PointY bi edge
  | PointZ => owned_read_run size PointZ bi edge
  end.
Definition owned_read_result size k bi edge : res :=
  match owned_read_tree size k bi edge with
  | Some rr => rr
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal
  end.

Lemma owned_read_tree_nonempty size k bi edge :
  match owned_read_tree size k bi edge with Some _ => true | None => false end = true.
Proof. destruct k; reflexivity. Qed.
Lemma owned_read_run_eq size k bi edge :
  owned_read_run size k bi edge = Some (owned_read_result size k bi edge).
Proof. destruct k; reflexivity. Qed.
Lemma owned_read_selected_log size k bi edge rho layout :
  slog (fst (rsel rho layout (owned_read_result size k bi edge))) = read_fe_log bi edge.
Proof.
  apply all_leaf_logs_selected.
  destruct k; repeat split; reflexivity.
Qed.
Lemma owned_read_selected_return size k bi edge rho layout :
  (stemps (fst (rsel rho layout (owned_read_result size k bi edge))))!1%positive = None.
Proof.
  apply all_leaf_property_selected with
    (P := fun state => (stemps state)!1%positive = None).
  destruct k; repeat split; reflexivity.
Qed.
Definition owned_read_storage_shape size state : Prop :=
  length (sregs state) = 2%nat /\
  rfree (nth 0 (sregs state) (mkreg [] true None)) = Some size /\
  rfree (nth 1 (sregs state) (mkreg [] true None)) = Some 16.
Lemma owned_read_leaf_storage size k bi edge :
  all_leaf_property (owned_read_storage_shape size) (owned_read_result size k bi edge).
Proof. destruct k; repeat split; reflexivity. Qed.
Lemma owned_read_selected_storage size k bi edge rho layout :
  owned_read_storage_shape size (fst (rsel rho layout (owned_read_result size k bi edge))).
Proof. apply all_leaf_property_selected; apply owned_read_leaf_storage. Qed.
Lemma owned_read_field_storage_size size k bi edge :
  point_coordinate_offset k + 40 <= size ->
  Forall (fun c => cofs c + size_chunk (cchunk c) <= size)
    (rcells (hd (mkreg [] true None) (owned_read_initial_regs size k bi edge))).
Proof. intros HS; destruct k; repeat constructor; cbn in *; lia. Qed.

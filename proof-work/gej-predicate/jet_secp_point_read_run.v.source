(** Original field reader at a coordinate inside one real owned point region. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Memory Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_point_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_read_initial_regs k bi edge : list region :=
  let delta := point_coordinate_offset k in
  [free_region
     (mkreg [mkcell delta Mint64 None; mkcell (delta+8) Mint64 None;
       mkcell (delta+16) Mint64 None; mkcell (delta+24) Mint64 None;
       mkcell (delta+32) Mint64 None] true None) 128;
   free_region (mkreg (mk_frame_cells (XA bi edge) Int64.zero) true None) 16].
Definition point_read_run k bi edge : option res :=
  xfun (genv_cenv secp_ge) [] read_fe_table 400 f_read_fe
    [XP 0 (point_coordinate_offset k); XP 1 0]
    (point_read_initial_regs k bi edge) [] 1.
Definition point_read_tree := Eval vm_compute in fun k bi edge =>
  match k with
  | PointX => point_read_run PointX bi edge
  | PointY => point_read_run PointY bi edge
  | PointZ => point_read_run PointZ bi edge
  end.
Definition point_read_result k bi edge : res :=
  match point_read_tree k bi edge with
  | Some rr => rr
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal
  end.

Lemma point_read_tree_nonempty k bi edge :
  match point_read_tree k bi edge with Some _ => true | None => false end = true.
Proof. destruct k; reflexivity. Qed.
Lemma point_read_run_eq k bi edge :
  point_read_run k bi edge = Some (point_read_result k bi edge).
Proof. destruct k; reflexivity. Qed.
Lemma point_read_selected_log k bi edge rho layout :
  slog (fst (rsel rho layout (point_read_result k bi edge))) = read_fe_log bi edge.
Proof.
  apply all_leaf_logs_selected.
  destruct k; repeat split; reflexivity.
Qed.
Lemma point_read_selected_return k bi edge rho layout :
  (stemps (fst (rsel rho layout (point_read_result k bi edge))))!1%positive = None.
Proof.
  apply all_leaf_property_selected with
    (P := fun state => (stemps state)!1%positive = None).
  destruct k; repeat split; reflexivity.
Qed.
Definition point_read_storage_shape state : Prop :=
  length (sregs state) = 2%nat /\
  rfree (nth 0 (sregs state) (mkreg [] true None)) = Some 128 /\
  rfree (nth 1 (sregs state) (mkreg [] true None)) = Some 16.
Lemma point_read_leaf_storage k bi edge :
  all_leaf_property point_read_storage_shape (point_read_result k bi edge).
Proof.
  destruct k; repeat split; reflexivity.
Qed.
Lemma point_read_selected_storage k bi edge rho layout :
  point_read_storage_shape (fst (rsel rho layout (point_read_result k bi edge))).
Proof. apply all_leaf_property_selected; apply point_read_leaf_storage. Qed.
Lemma point_read_field_storage_size k bi edge :
  Forall (fun c => cofs c + size_chunk (cchunk c) <= 128)
    (rcells (hd (mkreg [] true None) (point_read_initial_regs k bi edge))).
Proof. destruct k; repeat constructor; cbn; lia. Qed.

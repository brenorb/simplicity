(** Actual updated source-frame loads from the original reader's final rep. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_local_regions C.jet_secp_wrapper_run.
Require Import C.jet_frame_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma local_read_leaf_source bi edge :
  all_leaf_property (fun state =>
    rcells (nth 1 (sregs state) (mkreg [] true None)) =
      mk_frame_cells (XA bi edge) (Int64.repr 256)) (local_read_result bi edge).
Proof. split; [split; reflexivity|reflexivity]. Qed.

Lemma local_read_selected_source rho layout bi edge :
  rcells (nth 1 (sregs (fst (rsel rho layout (local_read_result bi edge))))
    (mkreg [] true None)) = mk_frame_cells (XA bi edge) (Int64.repr 256).
Proof. apply all_leaf_property_selected; apply local_read_leaf_source. Qed.

Lemma local_read_final_source_fields m ba bl bi edge rc rho :
  rho 0%nat = Int64.repr rc ->
  rep rho [(ba,0);(bl,0)]
    (sregs (fst (rsel rho (lay [(ba,0);(bl,0)])
      (local_read_result bi (Ptrofs.repr edge))))) m ->
  frame_fields_at m bl 0 bi edge (rc+256).
Proof.
  intros HR HRep.
  set (regs := sregs (fst (rsel rho (lay [(ba,0);(bl,0)])
    (local_read_result bi (Ptrofs.repr edge))))) in *.
  assert (HCount : length regs = 2%nat).
  { exact (proj1 (local_read_selected_storage rho (lay [(ba,0);(bl,0)])
      bi (Ptrofs.repr edge))). }
  assert (HIndex : (1 < length regs)%nat) by (rewrite HCount; lia).
  pose proof (nth_error_nth' regs (mkreg [] true None) HIndex) as HNth.
  pose proof (rep_region rho [(ba,0);(bl,0)] regs m 1 _ HRep HNth) as HRegion.
  assert (HCells : rcells (nth 1 regs (mkreg [] true None)) =
    mk_frame_cells (XA bi (Ptrofs.repr edge)) (Int64.repr 256)).
  { apply local_read_selected_source. }
  pose proof (region_load rho [(ba,0);(bl,0)] m 1 _ 0 Mint64
    (XA bi (Ptrofs.repr edge)) HRegion ltac:(rewrite HCells; cbn; auto)) as HP.
  pose proof (region_load rho [(ba,0);(bl,0)] m 1 _ 8 Mint64
    (XLb Badd (XLv 0%nat) (XLc (Int64.repr 256))) HRegion
    ltac:(rewrite HCells; cbn; auto)) as HC.
  change (Mem.load Mint64 m bl 0 = Some (Vptr bi (Ptrofs.repr edge))) in HP.
  change (Mem.load Mint64 m bl 8 =
    Some (Vlong (Int64.add (rho 0%nat) (Int64.repr 256)))) in HC.
  assert (HAdd : Int64.add (Int64.repr rc) (Int64.repr 256) = Int64.repr (rc+256)).
  { rewrite Int64.add_unsigned. apply Int64.eqm_samerepr.
    apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr. }
  rewrite HR, HAdd in HC.
  split; assumption.
Qed.

(** Initial original-reader representation from actual enclosing ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_frame_layout C.jet_output_layout.
Require Import C.jet_secp_b32_exec C.jet_secp_wrapper_storage C.jet_secp_wrapper_run.
Require Import C.jet_secp_local_regions C.jet_secp_point_write_run C.jet_secp_owned_read_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem owned_read_initial_rep_from_storage size k bits rc m ba bl bi edge :
  point_coordinate_offset k + 40 <= size ->
  Mem.range_perm m ba 0 size Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  rep (read_fe_rho bits rc) [(ba,0);(bl,0)]
    (owned_read_initial_regs size k bi (Ptrofs.repr edge)) m.
Proof.
  intros HSize HPointFree HFrameFree HFields HSeparate.
  assert (HMax : 128 <= Ptrofs.max_unsigned).
  { change (128 <= 18446744073709551615); lia. }
  pose proof (point_coordinate_offset_bounds k) as HBounds.
  pose proof (freeable_range_writable _ _ _ _ HPointFree) as HPointWrite.
  unfold owned_read_initial_regs.
  apply two_region_rep_separate; [reflexivity|exact HSeparate| |].
  - apply region_with_freeable.
    + unfold region_ok. cbn [bas blk lay nth fst snd rcells rw rfree].
      split; [change (0 <= 0); lia|].
      split; [eapply Mem.perm_valid_block; apply (HPointFree 0); lia|].
      split; [destruct k; reflexivity|]. split; [|exact I].
      apply Forall_forall. intros c HC.
      destruct k; cbn [point_coordinate_offset In] in HC;
        cbn [point_coordinate_offset] in HSize,HBounds;
        repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
        try contradiction; subst c;
        apply writable_undefined_cell;
        cbn [bas blk lay nth fst snd size_chunk align_chunk]; try lia.
      all: try (intros pos HPos; apply HPointWrite; lia).
      all: match goal with |- (8 | ?offset) => exists (offset / 8); reflexivity end.
    + reflexivity.
    + reflexivity.
    + exact HPointFree.
    + destruct k; cbn [point_coordinate_offset] in HSize; repeat constructor; cbn; lia.
  - apply region_with_freeable.
    + apply read_fe_region_from_frame; cbn [bas blk lay nth fst snd].
      * lia.
      * exists 0; reflexivity.
      * change (16 <= 18446744073709551615); lia.
      * apply freeable_range_writable; exact HFrameFree.
      * exact HFields.
    + reflexivity.
    + reflexivity.
    + exact HFrameFree.
    + apply frame_cells_storage_size.
Qed.
Print Assumptions owned_read_initial_rep_from_storage.

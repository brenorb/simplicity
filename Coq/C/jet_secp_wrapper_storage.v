(** Initial symbolic regions derived from ordinary frame and field storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep.
Require Import C.jet_frame_layout C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_b32.
Require Import C.jet_secp_wrapper_run C.jet_secp_b32_exec.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Lemma read_fe_region_from_frame bits rc layout m r bi edge :
  0 <= bas layout r -> (8 | bas layout r) -> bas layout r + 16 <= Ptrofs.max_unsigned ->
  Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 16) Cur Writable ->
  frame_fields_at m (blk layout r) (bas layout r) bi edge rc ->
  region_ok (read_fe_rho bits rc) layout m r
    (mkreg (mk_frame_cells (XA bi (Ptrofs.repr edge)) Int64.zero) true None).
Proof.
  intros HBase HAlign HMax HPerm [HEdge HCursor].
  change (region_ok (read_fe_rho bits rc) layout m r
    (mkreg (u64_cells 0 [XA bi (Ptrofs.repr edge); XLb Badd (XLv 0) (XLc Int64.zero)]) true None)).
  apply region_u64.
  - exact HBase.
  - exact HAlign.
  - change (bas layout r + 16 <= Ptrofs.max_unsigned); exact HMax.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - change (Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 16) Cur Writable); exact HPerm.
  - intros [|[|i]] x HNth; cbn [nth_error] in HNth.
    + inversion HNth; subst x; split; [|reflexivity].
      change (Mem.load Mint64 m (blk layout r) (bas layout r + 0) =
        Some (Vptr bi (Ptrofs.repr edge))).
      rewrite Z.add_0_r; exact HEdge.
    + inversion HNth; subst x; split; [|reflexivity].
      change (Mem.load Mint64 m (blk layout r) (bas layout r + 8) =
        Some (Vlong (Int64.add (Int64.repr rc) Int64.zero))).
      rewrite Int64.add_zero; exact HCursor.
    + destruct i; discriminate.
Qed.
Theorem read_fe_initial_rep_from_storage bits rc m bfe feofs bframe frameofs bi edge :
  0 <= feofs -> (8 | feofs) -> feofs + 40 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bfe feofs (feofs + 40) Cur Writable ->
  0 <= frameofs -> (8 | frameofs) -> frameofs + 16 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bframe frameofs (frameofs + 16) Cur Writable ->
  frame_fields_at m bframe frameofs bi edge rc -> bfe <> bframe ->
  rep (read_fe_rho bits rc) [(bfe, feofs); (bframe, frameofs)]
    (read_fe_initial_regs bi (Ptrofs.repr edge)) m.
Proof.
  intros HFeBase HFeAlign HFeMax HFePerm HFrameBase HFrameAlign HFrameMax HFramePerm HFrame HSeparate.
  apply two_region_rep_separate; [reflexivity|exact HSeparate| |].
  - apply region_fe_undefined_from_storage; assumption.
  - apply read_fe_region_from_frame; assumption.
Qed.

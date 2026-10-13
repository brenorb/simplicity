(** Preserve another coordinate across the original field-slice writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_point_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_coordinate_disjoint k j : k <> j ->
  point_coordinate_offset j + 40 <= point_coordinate_offset k \/
  point_coordinate_offset k + 40 <= point_coordinate_offset j.
Proof. destruct k, j; cbn; intros H; try contradiction; lia. Qed.

Lemma point_write_foot_bounds k b bx pos :
  foot [(b,0)] (map rshape (point_write_initial_regs k)) bx pos ->
  bx = b /\ point_coordinate_offset k <= pos < point_coordinate_offset k + 40.
Proof.
  intros (r & s & d & ch & HN & HC & HB & HR).
  destruct r as [|r]; [|destruct r; discriminate].
  change (bx = b) in HB; subst bx.
  split; [reflexivity|].
  destruct k; cbn [point_write_initial_regs point_coordinate_offset free_region
    u64_cells vars5 rshape rcells rw rfree map nth_error cshape cofs cchunk] in HN;
    inversion HN; subst s;
    cbn [fst] in HC;
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
    inversion HC; subst d ch;
    cbn [bas lay nth fst snd] in HR;
    change (size_chunk Mint64) with 8 in HR;
    cbn [point_coordinate_offset]; lia.
Qed.

Lemma point_write_preserves_zero_field m mf m0 bd bw bi b k j :
  k <> j ->
  fe_at m b (point_coordinate_offset j) (repeat Int64.zero 5) ->
  Mem.range_perm mf b 0 128 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  lframe (frame (extA m0 bd bw bi) [(b,0)] (point_write_initial_regs k) m) m mf ->
  fe_at mf b (point_coordinate_offset j) (repeat Int64.zero 5).
Proof.
  intros HD (HB & HA & HM & HP & HL) HF HS HFrame.
  assert (HV : Mem.valid_block m b).
  { eapply Mem.perm_valid_block. apply (HP (point_coordinate_offset j)); lia. }
  assert (HNotExt : ~ extA m0 bd bw bi b).
  { exact (HS 0%nat ltac:(cbn;lia)). }
  pose proof (point_coordinate_offset_bounds j) as HBounds.
  pose proof (point_coordinate_disjoint k j HD) as HDisjoint.
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable.
    intros ofs HOfs; apply HF; lia.
  - intros i x HI.
    assert (HIndex : (i < 5)%nat).
    { rewrite <- (repeat_length Int64.zero 5); apply (proj1 (nth_error_Some _ _)); rewrite HI; discriminate. }
    assert (HZ : 0 <= Z.of_nat i < 5) by (pose proof (Nat2Z.is_nonneg i); lia).
    rewrite (proj1 HFrame Mint64 b (point_coordinate_offset j + 8 * Z.of_nat i) HV).
    + apply HL; exact HI.
    + intros pos HPos. unfold frame. split; [exact HV|]. split; [|exact HNotExt].
      intro HFoot. destruct (point_write_foot_bounds k b b pos HFoot) as [_ HRange].
      change (size_chunk Mint64) with 8 in HPos. destruct HDisjoint; lia.
Qed.
Print Assumptions point_write_preserves_zero_field.

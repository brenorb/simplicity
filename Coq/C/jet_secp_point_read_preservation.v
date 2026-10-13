(** Preserve other coordinates while reading into the same real point allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation.
Require Import C.jet_secp_point_read_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_read_foot_bounds k b bl bi edge bx pos :
  foot [(b,0);(bl,0)] (map rshape (point_read_initial_regs k bi edge)) bx pos ->
  bx = bl \/
    (bx = b /\ point_coordinate_offset k <= pos < point_coordinate_offset k + 40).
Proof.
  intros (r & s & d & ch & HN & HC & HB & HR).
  destruct r as [|[|r]].
  - right. change (bx = b) in HB; subst bx.
    split; [reflexivity|].
    destruct k; cbn [point_read_initial_regs point_coordinate_offset free_region
      rshape rcells rw rfree map nth_error cshape cofs cchunk] in HN;
      inversion HN; subst s; cbn [fst] in HC;
      destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth fst snd] in HR;
      change (size_chunk Mint64) with 8 in HR;
      cbn [point_coordinate_offset]; lia.
  - left. exact HB.
  - cbn [point_read_initial_regs map nth_error] in HN. destruct r; discriminate.
Qed.

Lemma point_read_preserves_field m mf m0 bd bw bi b bl edge k j xs :
  k <> j -> b <> bl -> (length xs <= 5)%nat ->
  fe_at m b (point_coordinate_offset j) xs ->
  Mem.range_perm mf b 0 128 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0);(bl,0)] ->
  lframe (frame (extA m0 bd bw bi) [(b,0);(bl,0)]
    (point_read_initial_regs k bi (Ptrofs.repr edge)) m) m mf ->
  fe_at mf b (point_coordinate_offset j) xs.
Proof.
  intros HD HBL HLen (HB & HA & HM & HP & HL) HF HS HFrame.
  assert (HV : Mem.valid_block m b).
  { eapply Mem.perm_valid_block. apply (HP (point_coordinate_offset j)); lia. }
  assert (HNotExt : ~ extA m0 bd bw bi b).
  { exact (HS 0%nat ltac:(cbn; lia)). }
  pose proof (point_coordinate_offset_bounds j) as HBounds.
  pose proof (point_coordinate_disjoint k j HD) as HDisjoint.
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable. intros ofs HOfs; apply HF; lia.
  - intros i x HI.
    assert (HIndex : (i < length xs)%nat).
    { apply (proj1 (nth_error_Some _ _)); rewrite HI; discriminate. }
    assert (HZ : 0 <= Z.of_nat i < 5) by (pose proof (Nat2Z.is_nonneg i); lia).
    rewrite (proj1 HFrame Mint64 b (point_coordinate_offset j + 8 * Z.of_nat i) HV).
    + apply HL; exact HI.
    + intros pos HPos. unfold frame. split; [exact HV|]. split; [|exact HNotExt].
      intro HFoot.
      destruct (point_read_foot_bounds k b bl bi (Ptrofs.repr edge) b pos HFoot)
        as [HBlock|[_ HRange]]; [contradiction|].
      change (size_chunk Mint64) with 8 in HPos. destruct HDisjoint; lia.
Qed.
Print Assumptions point_read_preserves_field.

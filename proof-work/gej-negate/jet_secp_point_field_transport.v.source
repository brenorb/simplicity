(** Shared transport of exact coordinate fields through load-preserving helpers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_sx_mem C.jet_sx_state.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_field_load_transport k m mf b xs :
  (length xs <= 5)%nat -> fe_at m b (point_coordinate_offset k) xs ->
  Mem.range_perm mf b 0 128 Cur Freeable ->
  (forall i, (i < 5)%nat ->
    Mem.load Mint64 mf b (point_coordinate_offset k+8*Z.of_nat i) =
    Mem.load Mint64 m b (point_coordinate_offset k+8*Z.of_nat i)) ->
  fe_at mf b (point_coordinate_offset k) xs.
Proof.
  intros HLen (HB & HA & HM & HP & HL) HF HLoads.
  split; [exact HB|]; split; [exact HA|]; split; [exact HM|]; split.
  - apply freeable_range_writable; intros pos HPos.
    apply HF; pose proof (point_coordinate_offset_bounds k); lia.
  - intros i x HN; rewrite HLoads; [apply HL;exact HN|].
    assert (i < length xs)%nat by (apply (proj1 (nth_error_Some _ _)); rewrite HN;discriminate).
    lia.
Qed.

Lemma point_pure_frame_preserves_field k j m mf b xs :
  k <> j -> (length xs <= 5)%nat -> fe_at m b (point_coordinate_offset j) xs ->
  Mem.range_perm mf b 0 128 Cur Freeable ->
  lframe (fun bx pos => ~ foot [(b,0)] (map C.jet_sx_state.rshape (point_write_initial_regs k)) bx pos) m mf ->
  fe_at mf b (point_coordinate_offset j) xs.
Proof.
  intros HD HLen HField HFree HFrame.
  assert (HValid : Mem.valid_block m b).
  { destruct HField as (_ & _ & _ & HP & _).
    eapply Mem.perm_valid_block; apply (HP (point_coordinate_offset j)); lia. }
  eapply point_field_load_transport; [exact HLen|exact HField|exact HFree|].
  intros i Hi; apply (proj1 HFrame); [exact HValid|].
  intros pos HPos HFoot.
  destruct (point_write_foot_bounds k b b pos HFoot) as [_ HRange].
  pose proof (point_coordinate_disjoint k j HD) as HDisjoint.
  change (size_chunk Mint64) with 8 in HPos.
  destruct HDisjoint; lia.
Qed.
Print Assumptions point_pure_frame_preserves_field.

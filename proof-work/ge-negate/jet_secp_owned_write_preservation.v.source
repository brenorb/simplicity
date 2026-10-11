(** Coordinate and external framing for a writer inside its actual allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation.
Require Import C.jet_secp_owned_field_slice C.jet_secp_owned_field_transport C.jet_secp_owned_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma owned_write_preserves_field size m mf m0 bd bw bi b k j limbs :
  k <> j -> point_coordinate_offset j + 40 <= size -> length limbs = 5%nat ->
  fe_at m b (point_coordinate_offset j) limbs ->
  Mem.range_perm mf b 0 size Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  lframe (frame (extA m0 bd bw bi) [(b,0)] (owned_write_initial_regs size k) m) m mf ->
  fe_at mf b (point_coordinate_offset j) limbs.
Proof.
  intros HD HFit HLen HField HF HS HFrame.
  assert (HV : Mem.valid_block m b).
  { destruct HField as (_ & _ & _ & HP & _).
    eapply Mem.perm_valid_block; apply (HP (point_coordinate_offset j)); lia. }
  assert (HNotExt : ~ extA m0 bd bw bi b).
  { exact (HS 0%nat ltac:(cbn;lia)). }
  pose proof (point_coordinate_disjoint k j HD) as HDisjoint.
  apply (owned_field_load_transport (point_coordinate_offset j) size m mf b limbs
    HFit ltac:(lia) HField HF).
  intros i HI. assert (HZ : 0 <= Z.of_nat i < 5) by
    (pose proof (Nat2Z.is_nonneg i);lia).
  apply (proj1 HFrame Mint64 b (point_coordinate_offset j+8*Z.of_nat i) HV).
  intros pos HPos. unfold frame; split; [exact HV|]. split; [|exact HNotExt].
  intro HFoot.
  destruct (owned_field_slice_foot_bounds (point_coordinate_offset k) size b b pos HFoot)
    as [_ HRange].
  change (size_chunk Mint64) with 8 in HPos; destruct HDisjoint; lia.
Qed.

Lemma owned_write_outside_owner size m mf m0 bd bw bi b k :
  lframe (frame (extA m0 bd bw bi) [(b,0)] (owned_write_initial_regs size k) m) m mf ->
  lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intro HF; eapply lframe_implies; [exact HF|].
  intros bx pos [HB HE] HV; unfold frame; split; [exact HV|]. split; [|exact HE].
  intro HFoot; apply HB.
  exact (proj1 (owned_field_slice_foot_bounds (point_coordinate_offset k) size b bx pos HFoot)).
Qed.
Print Assumptions owned_write_preserves_field.
Print Assumptions owned_write_outside_owner.

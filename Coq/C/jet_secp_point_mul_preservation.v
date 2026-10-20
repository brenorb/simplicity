(** Framing needed to compose coordinate multiplications on the same point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions.
Require Import C.jet_secp_point_write_run C.jet_secp_point_mul_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_mul_foot_bounds k bp bs bx pos :
  foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos ->
  (bx = bp /\ point_coordinate_offset k <= pos < point_coordinate_offset k + 40) \/ bx = bs.
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|r]].
  - change (bx = bp) in HB; subst bx; left; split; [reflexivity|].
    cbn [point_mul_regs map nth_error rshape rcells rw rfree] in HN; injection HN as <-.
    cbn [fst u64_cells C.jet_secp_fe_nv.vars5 map cshape cofs cchunk] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch;
      cbn [bas lay nth snd] in HO; change (size_chunk Mint64) with 8 in HO; lia.
  - right; exact HB.
  - destruct r; discriminate HN.
Qed.

Lemma point_mul_other_field k j m mf bp bs w :
  k <> j -> bp <> bs -> fe_at m bp (point_coordinate_offset j) (words5 w) ->
  Mem.range_perm mf bp 0 128 Cur Freeable ->
  lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf ->
  fe_at mf bp (point_coordinate_offset j) (words5 w).
Proof.
  intros HNe HSeparate (HB & HA & HM & HP & HL) HFree HF.
  assert (HD : point_coordinate_offset j + 40 <= point_coordinate_offset k \/
    point_coordinate_offset k + 40 <= point_coordinate_offset j).
  { destruct k, j; cbn; try (exfalso; apply HNe; reflexivity); lia. }
  assert (HV : Mem.valid_block m bp).
  { eapply Mem.perm_valid_block; apply (HP (point_coordinate_offset j)); lia. }
  split; [exact HB|]; split; [exact HA|]; split; [exact HM|]; split.
  - apply freeable_range_writable; intros pos HPos; apply HFree.
    pose proof (point_coordinate_offset_bounds j); lia.
  - intros i x HN.
    assert (HI : (i < length (words5 w))%nat) by (apply nth_error_Some; rewrite HN; discriminate).
    change (i < 5)%nat in HI.
    rewrite (proj1 HF Mint64 bp (point_coordinate_offset j + 8 * Z.of_nat i) HV).
    + apply HL; exact HN.
    + intros pos HPos HFoot.
      destruct (point_mul_foot_bounds k bp bs bp pos HFoot) as [[_ HRange]|HE]; [|contradiction].
      change (size_chunk Mint64) with 8 in HPos; destruct HD; lia.
Qed.

Lemma point_mul_external_frame k m mf bp bs :
  lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf ->
  lframe (fun bx _ => bx <> bp /\ bx <> bs) m mf.
Proof.
  intro HF; eapply lframe_implies; [exact HF|].
  intros bx pos [HBP HBS] HV HFoot.
  destruct (point_mul_foot_bounds k bp bs bx pos HFoot) as [[HE _]|HE]; contradiction.
Qed.

Lemma point_mul_external_field k m mf bp bs b w :
  b <> bp -> b <> bs -> fe_at m b 0 (words5 w) ->
  lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf ->
  fe_at mf b 0 (words5 w).
Proof.
  intros HBP HBS (HB & HA & HM & HP & HL) HF.
  pose proof (point_mul_external_frame k m mf bp bs HF) as HE.
  assert (HV : Mem.valid_block m b) by (eapply Mem.perm_valid_block; apply (HP 0); lia).
  split; [exact HB|]; split; [exact HA|]; split; [exact HM|]; split.
  - intros pos HPos; apply (proj1 (proj2 HE)); [exact HV|split; assumption|apply HP; exact HPos].
  - intros i x HN; rewrite (proj1 HE Mint64 b (0 + 8 * Z.of_nat i) HV).
    + apply HL; exact HN.
    + intros; split; assumption.
Qed.

Lemma point_mul_external_free k m mf bp bs b size :
  b <> bp -> b <> bs -> 0 < size -> Mem.range_perm m b 0 size Cur Freeable ->
  lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf ->
  Mem.range_perm mf b 0 size Cur Freeable.
Proof.
  intros HBP HBS HSize HP HF.
  pose proof (point_mul_external_frame k m mf bp bs HF) as HE.
  assert (HV : Mem.valid_block m b) by (eapply Mem.perm_valid_block; apply (HP 0); lia).
  intros pos HPos; apply (proj1 (proj2 HE)); [exact HV|split; assumption|apply HP; exact HPos].
Qed.

Lemma point_mul_flag k m mf bp bs flag : bp <> bs -> Mem.valid_block m bp ->
  Mem.load Mint32 m bp 120 = Some (Vint flag) ->
  lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf ->
  Mem.load Mint32 mf bp 120 = Some (Vint flag).
Proof.
  intros HNe HV HL HF; rewrite (proj1 HF Mint32 bp 120 HV); [exact HL|].
  intros pos HPos HFoot.
  destruct (point_mul_foot_bounds k bp bs bp pos HFoot) as [[_ HR]|HE]; [|contradiction].
  pose proof (point_coordinate_offset_bounds k); change (size_chunk Mint32) with 4 in HPos; lia.
Qed.

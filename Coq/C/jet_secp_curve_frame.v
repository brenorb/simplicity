(** Reusable memory frames for the actual affine curve-check call sequence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_eval.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_read_preservation.
Require Import C.jet_secp_curve_square C.jet_secp_curve_mul.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma curve_two_blocks regs ba bb bx pos : length regs = 2%nat ->
  foot [(ba,0);(bb,0)] (map rshape regs) bx pos -> bx=ba \/ bx=bb.
Proof.
  intros HL (r & sh & d & ch & HN & HC & HB & HO).
  assert (HI : (r < 2)%nat).
  { rewrite <- HL, <- (map_length rshape regs). apply nth_error_Some; rewrite HN; discriminate. }
  destruct r as [|[|r]]; [left; exact HB|right; exact HB|lia].
Qed.

Lemma curve_one_block regs ba bx pos : length regs = 1%nat ->
  foot [(ba,0)] (map rshape regs) bx pos -> bx=ba.
Proof.
  intros HL (r & sh & d & ch & HN & HC & HB & HO).
  assert (HI : (r < 1)%nat).
  { rewrite <- HL, <- (map_length rshape regs). apply nth_error_Some; rewrite HN; discriminate. }
  destruct r; [exact HB|lia].
Qed.

Lemma curve_frame_two regs ba bb m mf : length regs = 2%nat ->
  lframe (fun bx pos => ~ foot [(ba,0);(bb,0)] (map rshape regs) bx pos) m mf ->
  lframe (fun bx _ => bx<>ba /\ bx<>bb) m mf.
Proof.
  intros HL HF. eapply lframe_implies; [exact HF|].
  intros bx pos [HA HB] HV HP. destruct (curve_two_blocks regs ba bb bx pos HL HP); contradiction.
Qed.

Lemma curve_frame_one regs ba m mf : length regs = 1%nat ->
  lframe (fun bx pos => ~ foot [(ba,0)] (map rshape regs) bx pos) m mf ->
  lframe (fun bx _ => bx<>ba) m mf.
Proof.
  intros HL HF. eapply lframe_implies; [exact HF|].
  intros bx pos HA HV HP. apply HA; exact (curve_one_block regs ba bx pos HL HP).
Qed.

Lemma curve_keep_free P m mf b sz : 0 < sz -> Mem.range_perm m b 0 sz Cur Freeable ->
  lframe P m mf -> (forall pos, P b pos) -> Mem.range_perm mf b 0 sz Cur Freeable.
Proof.
  intros HS HP HF HB pos HPos.
  assert (HV : Mem.valid_block m b) by (eapply Mem.perm_valid_block; apply (HP 0); lia).
  apply (proj1 (proj2 HF)); [exact HV|apply HB|apply HP; exact HPos].
Qed.

Lemma curve_keep_field_range P m mf b ofs xs : length xs = 5%nat ->
  fe_at m b ofs xs -> lframe P m mf ->
  (forall pos, ofs <= pos < ofs+40 -> P b pos) -> fe_at mf b ofs xs.
Proof.
  intros HLength (HB & HA & HM & HP & HL) HF HOutside.
  assert (HV : Mem.valid_block m b) by (eapply Mem.perm_valid_block; apply (HP ofs); lia).
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - intros pos HPos. apply (proj1 (proj2 HF)); [exact HV|apply HOutside; exact HPos|apply HP; exact HPos].
  - intros i x HN.
    assert (HI : (i < 5)%nat).
    { rewrite <- HLength. apply nth_error_Some; rewrite HN; discriminate. }
    assert (HZ : 0 <= Z.of_nat i < 5) by (pose proof (Nat2Z.is_nonneg i); lia).
    rewrite (proj1 HF Mint64 b (ofs+8*Z.of_nat i) HV); [apply HL; exact HN|].
    intros pos HPos. apply HOutside. change (size_chunk Mint64) with 8 in HPos; lia.
Qed.

Lemma curve_square_foot k bout bin bx pos :
  foot [(bout,0);(bin,0)] (map rshape (curve_square_regs k)) bx pos ->
  (bx=bout /\ 0 <= pos < 40) \/
  (bx=bin /\ curve_square_offset k <= pos < curve_square_offset k+40).
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|r]].
  - left. split; [exact HB|].
    cbn [curve_square_regs map nth_error rshape rcells rw rfree] in HN; injection HN as <-.
    cbn [fst map cshape cofs cchunk] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO; lia.
  - right. split; [exact HB|].
    cbn [curve_square_regs map nth_error rshape rcells rw rfree] in HN; injection HN as <-.
    cbn [curve_square_input rcells u64_cells vars5 rshape map cshape cofs cchunk fst] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO; lia.
  - destruct r; discriminate HN.
Qed.

Lemma curve_square_other_field k w m mf bout bin : bout<>bin ->
  fe_at m bin (curve_square_offset (negb k)) w -> length w=5%nat ->
  lframe (fun bx pos => ~ foot [(bout,0);(bin,0)] (map rshape (curve_square_regs k)) bx pos) m mf ->
  fe_at mf bin (curve_square_offset (negb k)) w.
Proof.
  intros HNe HF HLen HFrame. eapply curve_keep_field_range; [exact HLen|exact HF|exact HFrame|].
  intros pos HPos HFoot. destruct (curve_square_foot k bout bin bin pos HFoot) as [[HE _]|[_ HR]].
  - apply HNe; symmetry; exact HE.
  - destruct k; cbn [curve_square_offset negb] in *; lia.
Qed.

Lemma curve_mul_square_shape : map rshape curve_mul_regs = map rshape (curve_square_regs false).
Proof. reflexivity. Qed.

Lemma curve_mul_other_field w m mf bout bin : bout<>bin ->
  fe_at m bin 40 w -> length w=5%nat ->
  lframe (fun bx pos => ~ foot [(bout,0);(bin,0)] (map rshape curve_mul_regs) bx pos) m mf ->
  fe_at mf bin 40 w.
Proof.
  intros HNe HF HLen HFrame. rewrite curve_mul_square_shape in HFrame.
  exact (curve_square_other_field false w m mf bout bin HNe HF HLen HFrame).
Qed.

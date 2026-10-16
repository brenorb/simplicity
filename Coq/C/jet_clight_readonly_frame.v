(** Restore full load/permission framing on an initially readonly region.
    Readback alone does not promise survival; final readability is derived by callers. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Values Memory Clight ClightBigstep Events.
Require Import C.jet_sx_mem C.jet_clight_forward C.jet_clight_readonly.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition readonly_region_bounds (m : Mem.mem) b lo hi : Prop :=
  forall ofs k p, Mem.perm m b ofs k p <-> lo <= ofs < hi /\ perm_order Readable p.

Lemma readonly_bounds_not_writable m b lo hi :
  readonly_region_bounds m b lo hi -> forall ofs, ~ Mem.perm m b ofs Max Writable.
Proof.
  intros HB ofs HW; destruct (proj1 (HB ofs Max Writable) HW) as (_ & HO); inversion HO.
Qed.
Lemma readonly_bounds_transport m mf b lo hi :
  Mem.valid_block m b -> readonly_region_bounds m b lo hi -> mem_forward m mf ->
  Mem.range_perm mf b lo hi Cur Readable -> readonly_region_bounds mf b lo hi.
Proof.
  intros HV HB HF HP ofs k p; split.
  - intro HFinal; apply (proj1 (HB ofs Max p)).
    exact (proj2 (HF b HV) ofs p (Mem.perm_max _ _ _ _ _ HFinal)).
  - intros (HRange & HOrder); eapply Mem.perm_implies; [|exact HOrder].
    destruct k; [apply Mem.perm_cur_max; exact (HP ofs HRange)|exact (HP ofs HRange)].
Qed.
Lemma readonly_bounds_valid_access m mf b lo hi chunk ofs :
  readonly_region_bounds m b lo hi -> readonly_region_bounds mf b lo hi ->
  Mem.valid_access m chunk b ofs Readable -> Mem.valid_access mf chunk b ofs Readable.
Proof.
  intros HB HF (HP & HA); split; [|exact HA].
  intros i HI; apply (proj2 (HF i Cur Readable)); apply (proj1 (HB i Cur Readable)); exact (HP i HI).
Qed.

Theorem readonly_region_lframe m mf b lo hi :
  Mem.valid_block m b -> readonly_region_bounds m b lo hi ->
  Mem.range_perm mf b lo hi Cur Readable -> readonly_readback m mf ->
  lframe (fun block _ => block = b) m mf.
Proof.
  intros HV HB HP (HF & HBack).
  pose proof (readonly_bounds_transport m mf b lo hi HV HB HF HP) as HFinalBounds.
  split.
  - intros chunk block ofs HValid HBlock.
    assert (HE : block = b).
    { apply (HBlock ofs); pose proof (size_chunk_pos chunk); lia. }
    subst block.
    destruct (Mem.load chunk mf b ofs) as [v|] eqn:HLF.
    + destruct (Mem.load_loadbytes _ _ _ _ _ HLF) as (bytes & HBytes & HEq).
      pose proof (HBack b ofs (size_chunk chunk) bytes HV HBytes
        (fun i _ => readonly_bounds_not_writable m b lo hi HB i)) as HOldBytes.
      pose proof (Mem.load_valid_access _ _ _ _ _ HLF) as (_ & HAlign).
      rewrite (Mem.loadbytes_load chunk m b ofs bytes HOldBytes HAlign), <- HEq; reflexivity.
    + destruct (Mem.load chunk m b ofs) as [v|] eqn:HLM; [|reflexivity].
      pose proof (readonly_bounds_valid_access m mf b lo hi chunk ofs HB HFinalBounds
        (Mem.load_valid_access _ _ _ _ _ HLM)) as HAccess.
      destruct (Mem.valid_access_load _ _ _ _ HAccess) as (vf & HLoad); congruence.
  - split.
    + intros block ofs k p HValid -> HPerm.
      apply (proj2 (HFinalBounds ofs k p)); apply (proj1 (HB ofs k p)); exact HPerm.
    + intros block HValid; exact (proj1 (HF block HValid)).
Qed.
Theorem clight_funcall_readonly_lframe ge m f args t mf result b lo hi :
  Clight2.eval_funcall ge m f args t mf result ->
  Mem.valid_block m b -> readonly_region_bounds m b lo hi ->
  Mem.range_perm mf b lo hi Cur Readable -> lframe (fun block _ => block = b) m mf.
Proof.
  intros HC HV HB HP; apply (readonly_region_lframe m mf b lo hi HV HB HP).
  exact (proj2 (clight_exec_readonly_readback ge) m f args t mf result HC).
Qed.

Lemma lframe_add_block (P Q : block -> Z -> Prop) b m mf :
  lframe P m mf -> lframe (fun block _ => block = b) m mf ->
  (forall block ofs, block <> b -> Q block ofs -> P block ofs) -> lframe Q m mf.
Proof.
  intros (HL & HP & HV) (HBL & HBP & HBV) HQ; split.
  - intros chunk block ofs HValid HRange; destruct (peq block b) as [HE|HNe].
    + apply HBL; [exact HValid|intros; exact HE].
    + apply HL; [exact HValid|intros i HI; apply HQ; [exact HNe|exact (HRange i HI)]].
  - split; [|exact HV]. intros block ofs k p HValid HAt HPerm; destruct (peq block b) as [HE|HNe].
    + apply HBP; assumption.
    + apply HP; [exact HValid|apply HQ; assumption|exact HPerm].
Qed.

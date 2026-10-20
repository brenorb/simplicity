(** Establish public rescale's storage/frame invariants from its actual
    three allocations and by-value source-frame copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout
  C.jet_output_layout C.jet_frame_inv C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions.
Require Import C.jet_secp_rescale_public_entry C.jet_secp_rescale_public_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem rescale_prepare_public le m0 ma mb mc bl bp bc bd dbase bs sbase bw outedge cursor N bi edge rc :
  Mem.alloc m0 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,bp) -> Mem.alloc mb 0 40 = (mc,bc) ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  exists md,
    Clight2.exec_stmt secp_ge (rescale_public_env bl bp bc) le mc rescale_public_copy E0 le md Out_normal /\
    Mem.range_perm md bp 0 128 Cur Freeable /\ Mem.range_perm md bc 0 40 Cur Freeable /\
    Mem.range_perm md bl 0 16 Cur Freeable /\ frame_fields_at md bl 0 bi edge rc /\
    xsep (extA m0 bd bw bi) [(bp,0);(bc,0);(bl,0)] /\
    finv m0 bd dbase bw outedge cursor N bi md false [] /\
    lframe (fun b _ => b <> bp /\ b <> bc /\ b <> bl) m0 md.
Proof.
  intros HA HB HC HTemp HO HBase HAlign HFields.
  destruct (rescale_allocations_fresh m0 ma mb mc bl bp bc HA HB HC)
    as (HNewL & HNewP & HNewC & HPL & HCL & HPC).
  destruct (rescale_allocations_free m0 ma mb mc bl bp bc HA HB HC) as (HFL & HFP & HFC).
  pose proof (rescale_allocations_frame (fun _ _ => True) m0 ma mb mc bl bp bc HA HB HC) as HAlloc.
  assert (HSource : frame_fields_at mc bs sbase bi edge rc).
  { destruct HFields as [HE HR]; pose proof (load_valid m0 Mptr bs sbase _ HE) as HV.
    split; rewrite (proj1 HAlloc) by auto; assumption. }
  destruct HSource as [HEdge HCursor].
  destruct (frame_loadbytes_at mc bs sbase _ _ HEdge HCursor) as (bytes & HLoad).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLoad) as HLength.
  assert (HWritable : Mem.range_perm mc bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength; apply freeable_range_writable; exact HFL. }
  destruct (Mem.range_perm_storebytes mc bl 0 bytes HWritable) as (md & HStore).
  assert (HFrame : lframe (fun b _ => b <> bp /\ b <> bc /\ b <> bl) m0 md).
  { eapply lframe_trans; [eapply rescale_allocations_frame; eassumption|].
    apply lframe_unchanged; eapply Mem.storebytes_unchanged_on; [exact HStore|].
    intros pos HP [_ [_ HNL]]; apply HNL; reflexivity. }
  assert (HExt : eqext m0 bd bw bi m0 md).
  { eapply lframe_implies; [exact HFrame|].
    intros b pos [_ HV] _; repeat split; intro HE; subst b; contradiction. }
  assert (HU : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr; unfold frame_base_valid in HBase; lia. }
  exists md; split.
  - unfold rescale_public_copy; eapply exec_Sassign_copy.
    + apply eval_Evar_local; reflexivity.
    + apply eval_Etempvar; exact HTemp.
    + reflexivity.
    + eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
      * reflexivity.
      * intros _; change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)); rewrite HU; exact HAlign.
      * intros _; change (8 | 0); exists 0; reflexivity.
      * left; intro HE; apply HNewL; subst bs; exact (load_valid m0 Mptr bl sbase _ (proj1 HFields)).
      * change (Mem.loadbytes mc bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
        rewrite HU; exact HLoad.
      * exact HStore.
  - split.
    { intros pos HP; eapply Mem.perm_storebytes_1; [exact HStore|apply HFP; exact HP]. }
    split.
    { intros pos HP; eapply Mem.perm_storebytes_1; [exact HStore|apply HFC; exact HP]. }
    split.
    { intros pos HP; eapply Mem.perm_storebytes_1; [exact HStore|apply HFL; exact HP]. }
    split; [exact (frame_copy_fields_at mc md bs sbase bl bytes _ _ HLoad HStore HEdge HCursor)|].
    split.
    { intros [|[|[|r]]] HI; cbn [blk bas lay nth fst snd]; unfold extA, fext;
        [intros [_ HV]; contradiction|intros [_ HV]; contradiction|intros [_ HV]; contradiction|cbn in HI; lia]. }
    split; [eapply finv_stable; [exact HO|apply finv_init; exact HO|exact HExt]|exact HFrame].
Qed.

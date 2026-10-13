From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_gej_public_lifecycle C.jet_secp_gej_public_entry C.jet_secp_public_copy C.jet_secp_public_body.
Require Import C.jet_secp_local_regions.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Theorem gej_prepare_public_locals v_env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc
    :
  Mem.alloc m0 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,ba) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 768 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  exists mc,
    Clight2.exec_stmt secp_ge (gej_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb
      (Sassign (Evar jets_secp._src secp_frame_type) (Etempvar jets_secp._src secp_frame_type))
      E0 (secp_public_temps v_env bd dbase bs sbase) mc Out_normal /\
    Mem.range_perm mc ba 0 128 Cur Freeable /\ Mem.range_perm mc bl 0 16 Cur Freeable /\
    frame_fields_at mc bl 0 bi edge rc /\ ba <> bl /\
    xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] /\
    finv m0 bd dbase bw outedge cursor N bi mc false [] /\
    lframe (fun b _ => b <> ba /\ b <> bl) m0 mc /\
    ~ Mem.valid_block m0 ba /\ ~ Mem.valid_block m0 bl.
Proof.
  intros HA HB HOutput HCapacity HBase HAlign HFields.
  destruct (gej_alloc_fresh m0 ma bl ba mb HA HB) as [HFreshL [HFreshA HSeparate]].
  destruct (gej_alloc_freeable m0 ma bl ba mb HA HB) as [HFreeL HFreeA].
  pose proof (gej_alloc_source_fields m0 ma bl ba mb bs sbase bi edge rc HA HB HFields) as [HE HC].
  destruct (frame_loadbytes_at mb bs sbase _ _ HE HC) as [bytes HLoad].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLoad) as HLength.
  assert (HWritable : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength; apply freeable_range_writable; exact HFreeL. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes HWritable) as [mc HStore].
  assert (HFrame : lframe (fun b _ => b <> ba /\ b <> bl) m0 mc).
  { eapply lframe_trans.
    - eapply gej_alloc_lframe; eassumption.
    - apply lframe_unchanged; eapply Mem.storebytes_unchanged_on; [exact HStore|].
      intros pos HPos [_ HNot]; apply HNot; reflexivity. }
  assert (HExt : eqext m0 bd bw bi m0 mc).
  { eapply lframe_implies; [exact HFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mc; split.
  - apply exec_gej_public_copy with (bs := bs) (sbase := sbase) (bytes := bytes).
    + exact HBase.
    + exact HAlign.
    + intro HEqual; apply HFreshL; rewrite HEqual.
      exact (load_valid m0 Mptr bs sbase _ (proj1 HFields)).
    + reflexivity.
    + exact HLoad.
    + exact HStore.
  - split.
    { intros pos HPos; eapply Mem.perm_storebytes_1; [exact HStore|apply HFreeA; exact HPos]. }
    split.
    { intros pos HPos; eapply Mem.perm_storebytes_1; [exact HStore|apply HFreeL; exact HPos]. }
    split.
    { apply (frame_copy_fields_at mb mc bs sbase bl bytes _ _ HLoad HStore HE HC). }
    split; [exact HSeparate|]; split.
    { intros [|[|r]] HIndex; cbn [blk bas lay nth fst snd]; unfold extA, fext;
        [intros [_ HV]; contradiction|intros [_ HV]; contradiction|cbn in HIndex; lia]. }
    split.
    { eapply finv_stable; [exact HOutput|apply finv_init; exact HOutput|exact HExt]. }
    split; [exact HFrame|]; split; assumption.
Qed.

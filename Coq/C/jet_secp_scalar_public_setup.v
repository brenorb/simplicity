(* Caller-specific actual 16+32 allocation and source-copy preparation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_canonical_normalize.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_scalar_public_entry.
Local Opaque secp_ge.

Lemma scalar_alloc_lframe P m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,ba) -> lframe P m mb.
Proof.
  intros HA HB; eapply lframe_trans;
    apply lframe_unchanged; eapply Mem.alloc_unchanged_on; eassumption.
Qed.

Lemma scalar_alloc_fresh m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,ba) ->
  ~ Mem.valid_block m bl /\ ~ Mem.valid_block m ba /\ ba <> bl.
Proof.
  intros HA HB; split; [eapply Mem.fresh_block_alloc; exact HA|]; split.
  - intro HV; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    eapply Mem.valid_block_alloc; eassumption.
  - intro HE; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    rewrite HE; eapply Mem.valid_new_block; exact HA.
Qed.

Lemma scalar_alloc_freeable m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,ba) ->
  Mem.range_perm mb bl 0 16 Cur Freeable /\ Mem.range_perm mb ba 0 32 Cur Freeable.
Proof.
  intros HA HB; split; intros pos HPos.
  - eapply Mem.perm_alloc_1; [exact HB|]; eapply Mem.perm_alloc_2; eassumption.
  - eapply Mem.perm_alloc_2; eassumption.
Qed.

Lemma scalar_alloc_source_fields m ma bl ba mb bs base bi edge rc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,ba) ->
  frame_fields_at m bs base bi edge rc -> frame_fields_at mb bs base bi edge rc.
Proof.
  intros HA HB [HE HC].
  pose proof (load_valid m Mptr bs base _ HE) as HV.
  destruct (scalar_alloc_lframe (fun _ _ => True) m ma bl ba mb HA HB) as [HL _].
  split; rewrite HL by auto; assumption.
Qed.

Theorem scalar_prepare_public_locals le m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) :
  Mem.alloc m0 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,ba) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 1 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  le!jets_secp._src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  exists mc,
    Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le mb
      (Sassign (Evar jets_secp._src secp_frame_type) (Etempvar jets_secp._src secp_frame_type))
      E0 le mc Out_normal /\
    Mem.range_perm mc ba 0 32 Cur Freeable /\ Mem.range_perm mc bl 0 16 Cur Freeable /\
    frame_fields_at mc bl 0 bi edge rc /\ ba <> bl /\
    xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] /\
    invA m0 bd dbase bw outedge cursor N bi rc false [] 1
      (read_fe_rho (frame_input_word_bits value) rc) [] mc /\
    lframe (fun b _ => b <> ba /\ b <> bl) m0 mc /\
    ~ Mem.valid_block m0 ba /\ ~ Mem.valid_block m0 bl.
Proof.
  intros HA HB HOutput HCapacity HBase HAlign HFields HTemp.
  destruct (scalar_alloc_fresh m0 ma bl ba mb HA HB) as [HFreshL [HFreshA HSeparate]].
  destruct (scalar_alloc_freeable m0 ma bl ba mb HA HB) as [HFreeL HFreeA].
  pose proof (scalar_alloc_source_fields m0 ma bl ba mb bs sbase bi edge rc HA HB HFields) as [HE HC].
  destruct (frame_loadbytes_at mb bs sbase _ _ HE HC) as [bytes HLoad].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLoad) as HLength.
  assert (HWritable : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength; apply freeable_range_writable; exact HFreeL. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes HWritable) as [mc HStore].
  assert (HFrame : lframe (fun b _ => b <> ba /\ b <> bl) m0 mc).
  { eapply lframe_trans.
    - eapply scalar_alloc_lframe; eassumption.
    - apply lframe_unchanged; eapply Mem.storebytes_unchanged_on; [exact HStore|].
      intros pos HPos [_ HNot]; apply HNot; reflexivity. }
  assert (HExt : eqext m0 bd bw bi m0 mc).
  { eapply lframe_implies; [exact HFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mc; split.
  - apply exec_scalar_public_copy with (bs := bs) (sbase := sbase) (bytes := bytes).
    + exact HBase.
    + exact HAlign.
    + intro HEqual; apply HFreshL; rewrite HEqual.
      exact (load_valid m0 Mptr bs sbase _ (proj1 HFields)).
    + exact HTemp.
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
    { unfold invA; split; [reflexivity|]; split.
      - change (finv m0 bd dbase bw outedge cursor N bi mc false []).
        eapply finv_stable; [exact HOutput|apply finv_init; exact HOutput|exact HExt].
      - split; [exact HCapacity|cbn; lia]. }
    split; [exact HFrame|]; split; assumption.
Qed.

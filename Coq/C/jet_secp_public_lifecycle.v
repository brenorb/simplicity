(** Entry, by-value copy and local release for the unchanged public function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_canonical_normalize.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize Simplicity.Translate.encode.

Lemma secp_public_blocks bl ba :
  blocks_of_env secp_ge (secp_public_env bl ba) = [(bl,0,16);(ba,0,40)].
Proof. reflexivity. Qed.

Lemma secp_alloc_lframe P m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,ba) -> lframe P m mb.
Proof.
  intros HA HB; eapply lframe_trans;
    apply lframe_unchanged; eapply Mem.alloc_unchanged_on; eassumption.
Qed.

Lemma secp_alloc_fresh m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,ba) ->
  ~ Mem.valid_block m bl /\ ~ Mem.valid_block m ba /\ ba <> bl.
Proof.
  intros HA HB; split; [eapply Mem.fresh_block_alloc; exact HA|]; split.
  - intro HV; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    eapply Mem.valid_block_alloc; eassumption.
  - intro HE; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    rewrite HE; eapply Mem.valid_new_block; exact HA.
Qed.

Lemma secp_alloc_freeable m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,ba) ->
  Mem.range_perm mb bl 0 16 Cur Freeable /\ Mem.range_perm mb ba 0 40 Cur Freeable.
Proof.
  intros HA HB; split; intros pos HPos.
  - eapply Mem.perm_alloc_1; [exact HB|]; eapply Mem.perm_alloc_2; eassumption.
  - eapply Mem.perm_alloc_2; eassumption.
Qed.

Lemma secp_alloc_source_fields m ma bl ba mb bs base bi edge rc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,ba) ->
  frame_fields_at m bs base bi edge rc -> frame_fields_at mb bs base bi edge rc.
Proof.
  intros HA HB [HE HC].
  pose proof (load_valid m Mptr bs base _ HE) as HV.
  destruct (secp_alloc_lframe (fun _ _ => True) m ma bl ba mb HA HB) as [HL _].
  split; rewrite HL by auto; assumption.
Qed.

Lemma secp_free_public_locals m bl ba :
  ba <> bl -> Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m ba 0 40 Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (secp_public_env bl ba)) = Some mf /\
    lframe (fun b _ => b <> ba /\ b <> bl) m mf.
Proof.
  intros HSeparate HL HA.
  destruct (free_list_exists [(bl,0,16);(ba,0,40)] m) as [mf [HFree HUnchanged]].
  - cbn; repeat constructor; cbn; intuition congruence.
  - intros b lo hi [H|[H|H]]; [inversion H; subst; exact HL|inversion H; subst; exact HA|contradiction].
  - exists mf; split; [rewrite secp_public_blocks; exact HFree|].
    eapply lframe_implies; [apply lframe_unchanged; exact HUnchanged|].
    intros b pos [HA' HL'] HValid; cbn; intuition congruence.
Qed.

Theorem secp_prepare_public_locals v_env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) :
  Mem.alloc m0 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,ba) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  exists mc,
    Clight2.exec_stmt secp_ge (secp_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb
      (Sassign (Evar jets_secp._src secp_frame_type) (Etempvar jets_secp._src secp_frame_type))
      E0 (secp_public_temps v_env bd dbase bs sbase) mc Out_normal /\
    Mem.range_perm mc ba 0 40 Cur Freeable /\ Mem.range_perm mc bl 0 16 Cur Freeable /\
    frame_fields_at mc bl 0 bi edge rc /\ ba <> bl /\
    xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] /\
    invA m0 bd dbase bw outedge cursor N bi rc false [] 256
      (read_fe_rho (frame_input_word_bits value) rc) [] mc /\
    lframe (fun b _ => b <> ba /\ b <> bl) m0 mc /\
    ~ Mem.valid_block m0 ba /\ ~ Mem.valid_block m0 bl.
Proof.
  intros HA HB HOutput HCapacity HBase HAlign HFields.
  destruct (secp_alloc_fresh m0 ma bl ba mb HA HB) as [HFreshL [HFreshA HSeparate]].
  destruct (secp_alloc_freeable m0 ma bl ba mb HA HB) as [HFreeL HFreeA].
  pose proof (secp_alloc_source_fields m0 ma bl ba mb bs sbase bi edge rc HA HB HFields) as [HE HC].
  destruct (frame_loadbytes_at mb bs sbase _ _ HE HC) as [bytes HLoad].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLoad) as HLength.
  assert (HWritable : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength; apply freeable_range_writable; exact HFreeL. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes HWritable) as [mc HStore].
  assert (HFrame : lframe (fun b _ => b <> ba /\ b <> bl) m0 mc).
  { eapply lframe_trans.
    - eapply secp_alloc_lframe; eassumption.
    - apply lframe_unchanged; eapply Mem.storebytes_unchanged_on; [exact HStore|].
      intros pos HPos [_ HNot]; apply HNot; reflexivity. }
  assert (HExt : eqext m0 bd bw bi m0 mc).
  { eapply lframe_implies; [exact HFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mc; split.
  - apply exec_secp_public_copy with (bs := bs) (sbase := sbase) (bytes := bytes).
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
    { unfold invA; split; [reflexivity|]; split.
      - change (finv m0 bd dbase bw outedge cursor N bi mc false []).
        eapply finv_stable; [exact HOutput|apply finv_init; exact HOutput|exact HExt].
      - split; [exact HCapacity|cbn; lia]. }
    split; [exact HFrame|]; split; assumption.
Qed.

(** No helper execution, intermediate output, final permission or library
    oracle is assumed: all are derived from the original frame contract. *)
Theorem eval_secp_fe_normalize_canonical v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_normalize)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HOutput HCapacity HBase HAlign HFields HInput HCursor HMax.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb ba] eqn:HB.
  destruct (secp_prepare_public_locals v_env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
    HA HB HOutput HCapacity HBase HAlign HFields)
    as [mc [HCopy [HFreeA [HFreeL [HLocalFields [HSeparate [HSep [HInv [HPrepFrame [HFreshA HFreshL]]]]]]]]]].
  destruct (exec_secp_fe_normalize_rest_canonical (secp_public_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl
    eq_refl HOutput HInput HCursor HMax HFreeA HFreeL HLocalFields HSeparate HSep HInv)
    as [mw [HRest [HFinal [HFinalFreeA [HFinalFreeL HRestFrame]]]]].
  destruct (secp_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as [mf [HFree HFreeFrame]].
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := secp_public_env bl ba)
      (le1 := secp_public_temps v_env bd dbase bs sbase)
      (le2 := secp_public_temps v_env bd dbase bs sbase) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply secp_fe_normalize_entry; eassumption.
    + rewrite secp_fe_normalize_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := secp_public_temps v_env bd dbase bs sbase); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HOutput|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrepFrame|].
          intros b pos [HValid _] _; split; intro HEqual; subst b; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros b pos [HValid HExt] _; unfold secp_locals_outside.
            split; [intro HEqual; subst b; contradiction|]; split; [intro HEqual; subst b; contradiction|exact HExt].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HValid _] _; split; intro HEqual; subst b; contradiction. }
      eapply lframe_implies; [exact HOutside|]; intros b pos HExt HValid; split; assumption.
Qed.

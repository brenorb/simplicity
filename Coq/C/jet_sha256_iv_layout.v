(** Complete actual C sha_256_iv call against the canonical Simplicity scribe
    program, from initial frame permissions and arbitrary output contents. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_copy C.jet_frame_spec C.jet_frame_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_context C.jet_canonical C.jet_guarantees C.jet_constant_layout.
Require Import C.jet_sha256_iv_init C.jet_sha256_iv_exec C.jet_write32s_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_sha256_iv_layout_matches_spec env m bd dbase bs sbase bw edge cursor bytes :
  frame_base_valid sbase -> (8 | sbase) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  write_frame_at m bd dbase bw edge cursor 256 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_sha_256_iv)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cursor (encode (@sha256_iv_spec Alg.CoreFunSem tt)) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - 256) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - 256) / 64) \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign HB HFrame.
  pose proof HFrame as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw edge cursor 256 ltac:(lia) HFrame)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HB sbase); lia. }
  assert (HVd : Mem.valid_block m bd).
  { eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies with (p1 := Readable); [|constructor].
    eapply Mem.load_valid_access; exact HDE. }
  assert (HVw : Mem.valid_block m bw).
  { eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies with (p1 := Readable); [|constructor].
    eapply Mem.load_valid_access; exact HInitialWord. }
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 32) as [mb biv] eqn:HIV.
  assert (HLs : bl <> bs).
  { intro Heq; subst bs. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HVs). }
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HIOriginal : forall b, Mem.valid_block m b -> biv <> b).
  { intros b HV Heq; subst b. apply (Mem.fresh_block_alloc _ _ _ _ _ HIV).
    eapply Mem.valid_block_alloc; eauto. }
  assert (HIbl : biv <> bl).
  { intro Heq; subst biv. apply (Mem.fresh_block_alloc _ _ _ _ _ HIV).
    eapply Mem.valid_new_block; exact HA. }
  assert (HId : biv <> bd) by auto.
  assert (HIw : biv <> bw) by auto.
  assert (HBb : Mem.loadbytes mb bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [|exact HIV|].
    - erewrite Mem.loadbytes_alloc_unchanged; eauto.
    - eapply Mem.valid_block_alloc; eauto. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm mb bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_1; [exact HIV|]. eapply Mem.perm_alloc_2; eauto. }
  assert (PI : Mem.range_perm mb biv 0 32 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm mb bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes PLW) as [mc SC].
  assert (PIC : Mem.range_perm mc biv 0 32 Cur Writable).
  { intros ofs Hrange. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_implies; [apply PI; exact Hrange|constructor]. }
  destruct (eval_sha256_iv_init_layout mc biv 0 ltac:(lia)
    ltac:(change (32 <= 18446744073709551615); lia) ltac:(exists 0; reflexivity) PIC)
    as [mi [Hinit [Harray [HInitLoads [HInitPerm HInitValid]]]]].
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mi b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    rewrite HInitLoads by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [|exact SC|destruct Hb; subst; auto].
    erewrite Mem.load_alloc_unchanged; [|exact HIV|].
    - erewrite Mem.load_alloc_unchanged; [exact HL|exact HA|destruct Hb; subst; assumption].
    - eapply Mem.valid_block_alloc; [exact HA|destruct Hb; subst; assumption]. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mi b ofs kind p).
  { intros b ofs kind p HP. apply HInitPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; [exact HIV|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HFrameI : write_frame_at mi bd dbase bw edge cursor 256).
  { eapply write_frame_at_preserved; eauto. }
  assert (HWords : length sha256_iv_words = 8%nat) by reflexivity.
  assert (HCount : 32 * Z.of_nat (length sha256_iv_words) = 256) by (rewrite HWords; reflexivity).
  destruct (eval_write32s_layout mi biv 0 bd dbase bw edge cursor sha256_iv_words
    ltac:(lia) ltac:(rewrite HWords; change (32 <= 18446744073709551615); lia)
    HId HIw Harray ltac:(rewrite HCount; exact HFrameI))
    as [me [Hwrite [Houtput [Hprefix [Hfields [Hmemory [Hperm Hvalid]]]]]]].
  rewrite HCount in Hfields, Hmemory.
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm, HInitPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  assert (PIE : Mem.range_perm me biv 0 32 Cur Freeable).
  { intros ofs Hrange. apply Hperm, HInitPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PI; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mt HFreeS].
  assert (PIT : Mem.range_perm mt biv 0 32 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_free_1; [exact HFreeS|auto|exact (PIE ofs Hrange)]. }
  destruct (Mem.range_perm_free mt biv 0 32 PIT) as [mf HFreeIV].
  assert (HAfterLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk me b ofs = Some v -> Mem.load chunk mf b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    erewrite Mem.load_free; [|exact HFreeIV|destruct Hb; subst; auto].
    erewrite Mem.load_free; [exact HL|exact HFreeS|destruct Hb; subst; auto]. }
  exists mf. split.
  - eapply eval_sha256_iv_composes; eauto.
  - split.
    + rewrite sha256_iv_spec_cells. change (frame_output_cells_at mf bw edge cursor
        (uint32_word_cells sha256_iv_words)).
      eapply frame_output_cells_preserved; [|exact Houtput]. intros; eapply HAfterLoad; eauto.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros; eapply HBeforeLoad; eauto.
        -- intros; eapply HAfterLoad; eauto.
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split; eapply HAfterLoad; eauto.
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           assert (Hbiv : b <> biv) by (intro Heq; apply (HIOriginal b HV); congruence).
           erewrite Mem.load_free; [|exact HFreeIV|auto].
           erewrite Mem.load_free; [|exact HFreeS|auto].
           rewrite Hmemory by assumption. rewrite HInitLoads by auto.
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           erewrite Mem.load_alloc_unchanged; [|exact HIV|eapply Mem.valid_block_alloc; eauto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem sha256_iv_local_spec :
  jet_local_spec f_simplicity_sha_256_iv Ty.Unit (Word 8)
    (fun a => @sha256_iv_spec Alg.CoreFunSem a).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [] HB HA HF _ _ _ Hout.
  change (Z.of_nat (bitSize (Word 8))) with 256 in *.
  destruct (frame_fields_loadbytes _ _ _ _ _ _ HF) as [bytes Hbytes].
  exact (eval_sha256_iv_layout_matches_spec env m bd dbase bs sbase bw outedge cursor bytes
    HB HA Hbytes Hout).
Qed.

Theorem sha256_iv_context : jet_context_for f_simplicity_sha_256_iv (@sha256_iv_spec).
Proof.
  exact (jet_context _ _ sha256_iv_spec_parametric sha256_iv_local_spec ltac:(vm_compute; lia)).
Qed.
Definition sha256_iv_guarantees :=
  jet_local_spec_guarantees _ _ _ _ sha256_iv_local_spec.
Definition sha256_iv_context_guarantees :=
  jet_context_guarantees _ _ sha256_iv_spec_parametric sha256_iv_local_spec ltac:(vm_compute; lia).

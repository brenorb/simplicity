(** Complete actual eq_256 call against the canonical Generic.eq program.
    All allocation/copy/array-read/loop/write/free premises are derived from
    initial frames, including arbitrary valid cursors and unrelated bits. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_spec C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_writeBit_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_read16_input_word C.jet_readBit_layout.
Require Import C.jet_read32s_layout C.jet_word32_chunks C.jet_eq256_array C.jet_eq256_exec C.jet_equality_spec.
Require Import C.jet_uint32_array_init.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eq256_local_spec :
  jet_local_spec f_simplicity_eq_256 (Ty.Prod (Word 8) (Word 8)) Bit
    (fun xy => @equality_spec (Word 8) Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y]
    HSbase HSAlign HSource H0 Hmax Hin Hout.
  change (rc + 512 <= Int64.max_unsigned) in Hmax.
  change (write_frame_at m bd dbase bw outedge cursor 1) in Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  assert (Hword : @frame_input_word_at 9 m bi edge rc (x, y)).
  { apply frame_input_word_at_encode; exact Hin. }
  pose proof (Hword O _ (@frame_input_word_bits_nth 9 (x, y) O ltac:(vm_compute; lia))) as Hhead.
  replace (rc + Z.of_nat O) with rc in Hhead by lia.
  destruct Hhead as [_ [_ [sourceword [HSourceLoad _]]]].
  destruct HSource as [HSE HSO].
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hbyteslen.
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 1 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 64) as [mb ba] eqn:HArray.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HOriginal : forall b, Mem.valid_block m b -> ba <> b).
  { intros b HV Heq; subst b. apply (Mem.fresh_block_alloc _ _ _ _ _ HArray).
    eapply Mem.valid_block_alloc; eauto. }
  assert (HAbl : ba <> bl).
  { intro Heq; subst ba. apply (Mem.fresh_block_alloc _ _ _ _ _ HArray).
    eapply Mem.valid_new_block; exact HA. }
  assert (HAbd : ba <> bd) by (apply HOriginal; eapply load_valid_block; exact HDE).
  assert (HAbw : ba <> bw) by (apply HOriginal; eapply load_valid_block; exact HInitialWord).
  assert (HAbi : ba <> bi) by (apply HOriginal; eapply load_valid_block; exact HSourceLoad).
  assert (HSEb : Mem.load Mptr mb bs sbase = Some (Vptr bi (Ptrofs.repr edge))).
  { eapply Mem.load_alloc_other; [exact HArray|]. eapply Mem.load_alloc_other; eauto. }
  assert (HSOb : Mem.load Mint64 mb bs (sbase + 8) = Some (Vlong (Int64.repr rc))).
  { eapply Mem.load_alloc_other; [exact HArray|]. eapply Mem.load_alloc_other; eauto. }
  assert (HBb : Mem.loadbytes mb bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [|exact HArray|].
    - erewrite Mem.loadbytes_alloc_unchanged; [exact HB|exact HA|eapply load_valid_block; exact HSE].
    - eapply Mem.valid_block_alloc; [exact HA|eapply load_valid_block; exact HSE]. }
  assert (PL : Mem.range_perm mb bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_1; [exact HArray|].
    eapply Mem.perm_alloc_2; eauto. }
  assert (PA : Mem.range_perm mb ba 0 64 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm mb bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at mb mc bs sbase bl bytes _ _ HBb SC HSEb HSOb) as [HLE HLO].
  assert (HCopyLoad : forall ofs w, Mem.load Mint64 m bi ofs = Some (Vlong w) ->
    Mem.load Mint64 mc bi ofs = Some (Vlong w)).
  { intros ofs w HL. erewrite Mem.load_storebytes_other; [|exact SC|auto].
    eapply Mem.load_alloc_other; [exact HArray|]. eapply Mem.load_alloc_other; eauto. }
  assert (HWordC : @frame_input_word_at 9 mc bi edge rc (x, y)).
  { eapply frame_input_bits_at_preserved; eauto. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { split; [|exists 1; reflexivity].
    intros ofs Hrange. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_implies with (p1 := Freeable); [apply PL; cbn in Hrange; lia|constructor]. }
  assert (PAC : Mem.range_perm mc ba 0 64 Cur Writable).
  { intros ofs Hrange. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_implies; [apply PA; exact Hrange|constructor]. }
  assert (Hlen : length (word32_chunks 4 (x, y)) = 16%nat) by (apply word32_chunks_length).
  assert (HReadInput : forall j v, nth_error (word32_chunks 4 (x, y)) j = Some v ->
    frame_input_word_at mc bi edge (rc + 32 * Z.of_nat j) v).
  { apply frame_input_word32_chunks. apply frame_input_word_at_encode; exact HWordC. }
  destruct (eval_read32s_layout mc ba 0 bl 0 bi edge rc (word32_chunks 4 (x, y))
    ltac:(lia) ltac:(rewrite Hlen; change (64 <= 18446744073709551615); lia)
    ltac:(exists 0; reflexivity) ltac:(rewrite Hlen; exact PAC)
    ltac:(congruence) HLi HAbi HLocalBase H0 ltac:(rewrite Hlen; exact Hmax)
    (conj HLE HLO) PLC HReadInput)
    as (mr & Hread & HArrayR & HReadFields & HReadMemory & HReadPerm & HReadValid).
  rewrite Hlen in Hread.
  change (uint32_array_at mr ba 0
    (map word32_array_value (word32_chunks 3 x ++ word32_chunks 3 y))) in HArrayR.
  rewrite map_app in HArrayR.
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v Hb HL. rewrite HReadMemory.
    - erewrite Mem.load_storebytes_other; [|exact SC|destruct Hb; subst; auto].
      eapply Mem.load_alloc_other; [exact HArray|]. eapply Mem.load_alloc_other; eauto.
    - left; destruct Hb; subst; congruence.
    - left; destruct Hb; subst; congruence. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; [exact HArray|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr bd dbase bw outedge cursor 1).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_writeBit_layout mr bd dbase bw outedge cursor (eq256_array_result x y) HOutR)
    as (me & w & Hwrite & Hload & Hbit & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm, HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  assert (PAE : Mem.range_perm me ba 0 64 Cur Freeable).
  { intros ofs Hrange. apply Hperm, HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PA; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mt HFreeS].
  assert (PAT : Mem.range_perm mt ba 0 64 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_free_1; [exact HFreeS|auto|exact (PAE ofs Hrange)]. }
  destruct (Mem.range_perm_free mt ba 0 64 PAT) as [mf HFreeA].
  assert (HAfterLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk me b ofs = Some v -> Mem.load chunk mf b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    erewrite Mem.load_free; [|exact HFreeA|destruct Hb; subst; auto].
    erewrite Mem.load_free; [exact HL|exact HFreeS|destruct Hb; subst; auto]. }
  exists mf. split.
  - eapply eval_eq256_composes with
      (xs := map word32_array_value (word32_chunks 3 x))
      (ys := map word32_array_value (word32_chunks 3 y)); eauto.
  - split.
    + eapply frame_output_cells_preserved; [|].
      * intros ofs v HL. eapply HAfterLoad; eauto.
      * apply carry_output_encode; [lia|]. exists w. split; [exact Hload|].
        rewrite Hbit, eq256_array_denotes.
        destruct (@equality_spec (Word 8) Alg.CoreFunSem (x, y)) as [[]|[]]; reflexivity.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros; eapply HBeforeLoad; eauto.
        -- intros; eapply HAfterLoad; eauto.
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split; eapply HAfterLoad; eauto.
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           assert (Hba : b <> ba) by (intro Heq; apply (HOriginal b HV); congruence).
           erewrite Mem.load_free; [|exact HFreeA|auto].
           erewrite Mem.load_free; [|exact HFreeS|auto].
           rewrite Hmemory by assumption. rewrite HReadMemory by (left; assumption).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           erewrite Mem.load_alloc_unchanged; [|exact HArray|eapply Mem.valid_block_alloc; eauto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem eq256_context : jet_context_for f_simplicity_eq_256 (@equality_spec (Word 8)).
Proof.
  exact (jet_context _ _ (equality_spec_parametric (Word 8)) eq256_local_spec ltac:(vm_compute; lia)).
Qed.
Definition eq256_guarantees := jet_local_spec_guarantees _ _ _ _ eq256_local_spec.
Definition eq256_context_guarantees :=
  jet_context_guarantees _ _ (equality_spec_parametric (Word 8)) eq256_local_spec ltac:(vm_compute; lia).

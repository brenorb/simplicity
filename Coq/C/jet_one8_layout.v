(** Full one_8 equivalence at arbitrary valid source and output layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_spec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_write8_layout_total C.jet_one8_layout_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_one8_layout_matches_spec m bd dbase bs sbase bw edge cursor bytes :
  frame_base_valid sbase -> (8 | sbase) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  write_frame_at m bd dbase bw edge cursor 8 ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_one_8)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vundef] E0 mf (Vint Int.one) /\
    byte_output_at mf bw edge cursor (@one8_spec Alg.CoreFunSem tt) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - 8) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= byte_write_low edge cursor \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign HB HFrame.
  pose proof HFrame as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw edge cursor 8 ltac:(lia) HFrame)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HB sbase); lia. }
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs).
  { intro Heq; subst bs. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HVs). }
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p).
  { intros b ofs kind p HP. eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HFrameC : write_frame_at mc bd dbase bw edge cursor 8).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write8_layout mc bd dbase bw edge cursor Int.one HFrameC)
    as [me [Hwrite [Houtput [Hprefix [Hfields [Hmemory [Hperm Hvalid]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_one8_layout_composes; eauto.
  - split.
    + eapply byte_output_at_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * change (byte_output_at me bw edge cursor (decode_word8 (Int64.repr 1))) in Houtput.
        rewrite decode_word8_one in Houtput. exact Houtput.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HL. eapply HBeforeLoad; eauto.
        -- intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmemory by assumption.
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

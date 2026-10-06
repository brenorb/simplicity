(** Full one_16/one_32/one_64 equivalence at arbitrary non-wrapping layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_spec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_output_slice.
Require Import C.jet_write_wide_layout_total C.jet_one_wide_layout_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_one_wide_layout_matches_spec env s m bd dbase bs sbase bw edge cursor bytes :
  frame_base_valid sbase -> (8 | sbase) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  write_frame_at m bd dbase bw edge cursor (wide_bits s) ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_one s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    wide_output_at s mf bw edge cursor (@wide_one_spec s Alg.CoreFunSem tt) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - wide_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= slice_write_low (wide_bits s) edge cursor \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign HB HFrame. pose proof (wide_bits_bounds s) as HNbound.
  pose proof HFrame as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw edge cursor (wide_bits s) ltac:(lia) HFrame)
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
  assert (HFrameC : write_frame_at mc bd dbase bw edge cursor (wide_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write_wide_layout s mc bd dbase bw edge cursor Int64.one HFrameC)
    as [me [Hwrite [Houtput [Hprefix [Hfields [Hmemory [Hperm Hvalid]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_one_wide_layout_composes; eauto.
  - split.
    + eapply wide_output_at_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * exists (Int64.zero_ext (wide_bits s) Int64.one).
        split; [exact Houtput|apply decode_wide_one].
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

(** Complete generated C low/high calls against their Simplicity programs.
    Preconditions refer only to the initial memory; the output contents and
    valid non-wrapping cursor positions are arbitrary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_spec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant C.jet_constant_exec C.jet_constant_writer.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma frame_output_cells_preserved m mf bw edge cursor cells :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  frame_output_cells_at m bw edge cursor cells -> frame_output_cells_at mf bw edge cursor cells.
Proof.
  intros HP HO.
  assert (HB : forall q bit, frame_output_bit_at m bw edge q bit -> frame_output_bit_at mf bw edge q bit).
  { intros q bit [HQ [w [HL HE]]]. split; [exact HQ|]. exists w. split; [apply HP; exact HL|exact HE]. }
  intros i c Hi. specialize (HO i c Hi). destruct c as [bit|]; cbn [cell_matches] in *.
  - apply HB; exact HO.
  - destruct HO as [bit Hbit]. exists bit. apply HB; exact Hbit.
Qed.

Theorem eval_constant_layout_matches_spec env s high m bd dbase bs sbase bw edge cursor bytes :
  frame_base_valid sbase -> (8 | sbase) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  write_frame_at m bd dbase bw edge cursor (constant_bits s) ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal (constant_jet s high))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cursor (encode (@constant_spec s high Alg.CoreFunSem tt)) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - constant_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - constant_bits s) / 64) \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign HB HFrame. pose proof (constant_bits_bounds s) as HNbound.
  pose proof HFrame as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw edge cursor (constant_bits s) ltac:(lia) HFrame)
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
  assert (HFrameC : write_frame_at mc bd dbase bw edge cursor (constant_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_constant_writer s high mc bd dbase bw edge cursor HFrameC)
    as [me [Hwrite [Houtput [Hprefix [Hfields [Hmemory [Hperm Hvalid]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_constant_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved; [|exact Houtput].
      intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
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

Theorem constant_local_spec s high :
  jet_local_spec (constant_jet s high) Ty.Unit (Word (constant_log s))
    (fun a => @constant_spec s high Alg.CoreFunSem a).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [] HB HA HF _ _ _ Hout.
  rewrite constant_bitSize in *.
  destruct (frame_fields_loadbytes _ _ _ _ _ _ HF) as [bytes Hbytes].
  exact (eval_constant_layout_matches_spec env s high m bd dbase bs sbase bw outedge cursor bytes
    HB HA Hbytes Hout).
Qed.

Corollary low1_local_spec : jet_local_spec f_simplicity_low_1 Ty.Unit (Word 0)
  (fun a => @constant_spec C1 Datatypes.false Alg.CoreFunSem a).
Proof. exact (constant_local_spec C1 Datatypes.false). Qed.
Corollary high1_local_spec : jet_local_spec f_simplicity_high_1 Ty.Unit (Word 0)
  (fun a => @constant_spec C1 Datatypes.true Alg.CoreFunSem a).
Proof. exact (constant_local_spec C1 Datatypes.true). Qed.
Corollary low8_local_spec : jet_local_spec f_simplicity_low_8 Ty.Unit (Word 3)
  (fun a => @constant_spec C8 Datatypes.false Alg.CoreFunSem a).
Proof. exact (constant_local_spec C8 Datatypes.false). Qed.
Corollary high8_local_spec : jet_local_spec f_simplicity_high_8 Ty.Unit (Word 3)
  (fun a => @constant_spec C8 Datatypes.true Alg.CoreFunSem a).
Proof. exact (constant_local_spec C8 Datatypes.true). Qed.
Corollary low16_local_spec : jet_local_spec f_simplicity_low_16 Ty.Unit (Word 4)
  (fun a => @constant_spec C16 Datatypes.false Alg.CoreFunSem a).
Proof. exact (constant_local_spec C16 Datatypes.false). Qed.
Corollary high16_local_spec : jet_local_spec f_simplicity_high_16 Ty.Unit (Word 4)
  (fun a => @constant_spec C16 Datatypes.true Alg.CoreFunSem a).
Proof. exact (constant_local_spec C16 Datatypes.true). Qed.
Corollary low32_local_spec : jet_local_spec f_simplicity_low_32 Ty.Unit (Word 5)
  (fun a => @constant_spec C32 Datatypes.false Alg.CoreFunSem a).
Proof. exact (constant_local_spec C32 Datatypes.false). Qed.
Corollary high32_local_spec : jet_local_spec f_simplicity_high_32 Ty.Unit (Word 5)
  (fun a => @constant_spec C32 Datatypes.true Alg.CoreFunSem a).
Proof. exact (constant_local_spec C32 Datatypes.true). Qed.
Corollary low64_local_spec : jet_local_spec f_simplicity_low_64 Ty.Unit (Word 6)
  (fun a => @constant_spec C64 Datatypes.false Alg.CoreFunSem a).
Proof. exact (constant_local_spec C64 Datatypes.false). Qed.
Corollary high64_local_spec : jet_local_spec f_simplicity_high_64 Ty.Unit (Word 6)
  (fun a => @constant_spec C64 Datatypes.true Alg.CoreFunSem a).
Proof. exact (constant_local_spec C64 Datatypes.true). Qed.

Theorem constant_context s high : jet_context_for (constant_jet s high) (@constant_spec s high).
Proof.
  exact (jet_context _ _ (constant_spec_parametric s high) (constant_local_spec s high)
    ltac:(destruct s; vm_compute; lia)).
Qed.
Definition constant_guarantees s high :=
  jet_local_spec_guarantees _ _ _ _ (constant_local_spec s high).
Definition constant_context_guarantees s high :=
  jet_context_guarantees _ _ (constant_spec_parametric s high) (constant_local_spec s high)
    ltac:(destruct s; vm_compute; lia).

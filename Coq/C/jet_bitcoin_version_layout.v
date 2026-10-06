(** Initial-memory correctness of the actual Bitcoin version jet, against its
    canonical Version primitive. No intermediate execution premise is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_frame_copy C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_output_slice.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_write32_layout C.jet_bitcoin_version_spec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_bitcoin_version_layout_matches_primitive (environment : Bitcoin.env)
    m bd dbase bs sbase bw edge cursor be ebase bt txbase version bytes :
  frame_base_valid sbase -> (8 | sbase) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  0 <= ebase <= Ptrofs.max_unsigned -> 0 <= txbase -> txbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 m bt (txbase + 464) = Some (Vlong version) ->
  Int64.unsigned version = Int.unsigned (sigTxVersion (Bitcoin.envTx environment)) ->
  write_frame_at m bd dbase bw edge cursor 32 ->
  exists mf value,
    Bitcoin.sem Bitcoin.Version tt environment = Some value /\
    Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_bitcoin_version)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)]
      E0 mf (Vint Int.one) /\
    wide_output_at W32 mf bw edge cursor value /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - 32) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= slice_write_low 32 edge cursor \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign HB HEbase HTbase HTmax HEnv HVersion HR HFrame.
  pose proof HFrame as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw edge cursor 32 ltac:(lia) HFrame)
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
  assert (HBeforeLoad : forall chunk b ofs v,
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v).
  { intros chunk b ofs v HL.
    assert (Hbl : bl <> b) by (eapply fresh_frame_not_loaded; eauto).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p).
  { intros b ofs kind p HP. eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HFrameC : write_frame_at mc bd dbase bw edge cursor 32).
  { eapply write_frame_at_preserved with (m := m).
    - intros chunk b ofs v _ HL. apply HBeforeLoad; exact HL.
    - exact HBeforePerm.
    - exact HFrame. }
  destruct (eval_bitcoin_write32_layout mc bd dbase bw edge cursor version HFrameC)
    as [me [Hwrite [Houtput [Hprefix [Hfields [Hmemory [Hperm Hvalid]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf, (decode_wide W32 (Int64.zero_ext 32 version)). split.
  - symmetry. apply bitcoin_version_carrier_matches_primitive; exact HR.
  - split.
    { eapply eval_bitcoin_version_composes with (ma := ma) (mc := mc) (me := me)
        (bl := bl) (bt := bt) (txbase := txbase) (version := version) (bytes := bytes);
        eauto using HBeforeLoad. }
    { split.
    + eapply wide_output_at_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * exists (Int64.zero_ext 32 version).
        split; [exact Houtput|reflexivity].
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
    }
Qed.

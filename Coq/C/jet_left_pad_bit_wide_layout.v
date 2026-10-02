(** Complete left_pad_low_1_{16,32,64} calls under initial-only frame contracts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_complement1_exec C.jet_left_pad_bit_wide_exec C.jet_spec.
Require Import C.jet_readBit_layout C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_wide_left_pad_bit_layout_matches_spec env s m bd dbase bs sbase bi bw edge outedge
    (x : Ty.tySem (Word 0)) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 1 -> frame_input_bit_at m bi edge rc (Bit.toBool x) ->
  write_frame_at m bd dbase bw outedge cursor (wide_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_left_pad_bit s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@left_pad_low_1_n Alg.CoreFunSem (wide_log s) x)) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - wide_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - wide_bits s) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput Hout.
  pose proof (wide_bits_bounds s) as Hwidth.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (wide_bits s) ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct Hinput as [_ [_ [w [HL _]]]]. eapply fresh_frame_not_loaded; eauto. }
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_loadbytes_at ma bs sbase _ _ HSEa HSOa) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa) as [HLE HLO].
  assert (HInputC : frame_input_bit_at mc bi edge rc (Bit.toBool x)).
  { destruct Hinput as [HR [HEi [w [HL HX]]]].
    split; [exact HR|]. split; [exact HEi|]. exists w. split; [|exact HX].
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_readBit_layout mc bl 0 bi edge rc (Bit.toBool x) HLocalBase HRC (conj HLE HLO) HInputC PLC)
    as (mr & Hread & HReadFields & HReadMem & HReadPerm & HReadValid).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v Hb HL. rewrite HReadMem by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr bd dbase bw outedge cursor (wide_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write_wide_layout s mr bd dbase bw outedge cursor (bit_long (Bit.toBool x)) HOutR)
    as (me & Hwrite & Hslice & Hprefix & Hfields & HRawMemory & Hperm & Hvalid).
  assert (Houtput : frame_output_cells_at me bw outedge cursor
    (encode (@left_pad_low_1_n Alg.CoreFunSem (wide_log s) x))).
  { apply (wide_output_at_encode s); [lia|].
    exists (Int64.zero_ext (wide_bits s) (bit_long (Bit.toBool x))).
    split; [exact Hslice|apply wide_left_pad_bit_decode]. }
  assert (Hmemory : loads_outside_ranges mr me bd (dbase + 8) (dbase + 16)
    bw (outedge + 8 * ((cursor - wide_bits s) / 64)) (write_word_address outedge cursor + 8)).
  { intros chunk b ofs HB' HW'. apply HRawMemory; [exact HB'|].
    pose proof (slice_write_low_bound (wide_bits s) outedge cursor ltac:(lia) ltac:(lia)).
    destruct HW' as [HN|[HL|HH]]; [left|right; left|right; right]; auto; lia. }
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_wide_left_pad_bit_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * exact Houtput.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w' HL. eapply HBeforeLoad; eauto.
        -- intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmemory by assumption. rewrite HReadMem by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem wide_left_pad_bit_local_spec s :
  jet_local_spec (wide_left_pad_bit s) (Word 0) (Word (wide_log s))
    (fun x => @left_pad_low_1_n Alg.CoreFunSem (wide_log s) x).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 0))) with 1 in *.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in *
    by (destruct s; reflexivity).
  eapply eval_wide_left_pad_bit_layout_matches_spec; eauto; [lia|].
  specialize (Hin 0%nat (Some (Bit.toBool x)) ltac:(destruct x as [[]|[]]; reflexivity)).
  change (frame_input_bit_at m bi edge (rc + Z.of_nat 0) (Bit.toBool x)) in Hin.
  replace (rc + Z.of_nat 0) with rc in Hin by lia. exact Hin.
Qed.
Corollary left_pad_low_1_16_local_spec :
  jet_local_spec f_simplicity_left_pad_low_1_16 (Word 0) (Word 4)
    (fun x => @left_pad_low_1_n Alg.CoreFunSem 4 x).
Proof. exact (wide_left_pad_bit_local_spec W16). Qed.
Corollary left_pad_low_1_32_local_spec :
  jet_local_spec f_simplicity_left_pad_low_1_32 (Word 0) (Word 5)
    (fun x => @left_pad_low_1_n Alg.CoreFunSem 5 x).
Proof. exact (wide_left_pad_bit_local_spec W32). Qed.
Corollary left_pad_low_1_64_local_spec :
  jet_local_spec f_simplicity_left_pad_low_1_64 (Word 0) (Word 6)
    (fun x => @left_pad_low_1_n Alg.CoreFunSem 6 x).
Proof. exact (wide_left_pad_bit_local_spec W64). Qed.

Theorem wide_left_pad_bit_context s :
  jet_context_for (wide_left_pad_bit s) (fun term => @left_pad_low_1_n term (wide_log s)).
Proof.
  exact (jet_context _ _ (left_pad_low_1_n_parametric (wide_log s))
    (wide_left_pad_bit_local_spec s) ltac:(destruct s; vm_compute; lia)).
Qed.
Definition wide_left_pad_bit_guarantees s :=
  jet_local_spec_guarantees _ _ _ _ (wide_left_pad_bit_local_spec s).
Definition wide_left_pad_bit_context_guarantees s :=
  jet_context_guarantees _ _ (left_pad_low_1_n_parametric (wide_log s))
    (wide_left_pad_bit_local_spec s) ltac:(destruct s; vm_compute; lia).

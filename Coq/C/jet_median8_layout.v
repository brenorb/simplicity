(** Complete byte median equivalence from initial-only frame contracts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_frame_spec.
Require Import C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_write8_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_median_spec C.jet_median8_exec.
Require Import C.jet_minmax8_layout C.jet_order_spec C.jet_order8_exec C.jet_median_control.
Require Import C.jet_add8_word.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma median8_decode w z v :
  decode_word8 (Int64.repr (Int.unsigned (median8_payload
    (read8_result w) (read8_result z) (read8_result v)))) =
    @median_word_spec 3 Alg.CoreFunSem (decode_word8 w, (decode_word8 z, decode_word8 v)).
Proof.
  rewrite median_word_spec_strict. unfold median8_payload, median8_raw, median_decision, median_select.
  rewrite !order8_bit_numeric, !read8_result_unsigned. cbn [order_numeric].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    rewrite Int.zero_ext_idem by lia; apply byte_input_value_decode.
Qed.

Theorem eval_median8_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    (x y z : Ty.tySem Word8) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  byte_slice_at m bi edge rc x -> byte_slice_at m bi edge (rc + 8) y ->
  byte_slice_at m bi edge (rc + 16) z ->
  write_frame_at m bd dbase bw outedge cursor 8 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal median8)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@median_word_spec 3 Alg.CoreFunSem (x, (y, z)))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 8) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 8) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] Hinput1 Hinput2 Hinput3 Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 8 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct Hinput1 as [_ [_ [h [l [HL _]]]]]. eapply fresh_frame_not_loaded; eauto. }
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
  assert (HInputC1 : byte_slice_at mc bi edge rc x).
  { eapply byte_slice_preserved; [|exact Hinput1].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC1 : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_read8_byte_at mc bl 0 bi edge rc x HLocalBase (conj HLE HLO) HInputC1 PLC1 HLi)
    as (mr & payload1 & Hread1 & Hdecode1 & HReadFields1 & HReadMem1 & HReadPerm1 & HReadValid1).
  assert (HInputR2 : byte_slice_at mr bi edge (rc + 8) y).
  { eapply byte_slice_preserved; [|exact Hinput2].
    intros ofs w HL. rewrite HReadMem1 by (left; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC2 : Mem.valid_access mr Mint64 bl 8 Writable).
  { destruct PLC1 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm1. apply HP; exact Hrange. }
  destruct (eval_read8_byte_at mr bl 0 bi edge (rc + 8) y HLocalBase HReadFields1 HInputR2 PLC2 HLi)
    as (mr2 & payload2 & Hread2 & Hdecode2 & HReadFields2 & HReadMem2 & HReadPerm2 & HReadValid2).
  replace (rc + 8 + 8) with (rc + 16) in HReadFields2 by lia.
  assert (HInputR3 : byte_slice_at mr2 bi edge (rc + 16) z).
  { eapply byte_slice_preserved; [|exact Hinput3].
    intros ofs w HL. rewrite HReadMem2 by (left; congruence). rewrite HReadMem1 by (left; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC3 : Mem.valid_access mr2 Mint64 bl 8 Writable).
  { destruct PLC2 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm2. apply HP; exact Hrange. }
  destruct (eval_read8_byte_at mr2 bl 0 bi edge (rc + 16) z HLocalBase HReadFields2 HInputR3 PLC3 HLi)
    as (mr3 & payload3 & Hread3 & Hdecode3 & HReadFields3 & HReadMem3 & HReadPerm3 & HReadValid3).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr3 b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    rewrite HReadMem3 by (left; destruct Hb; subst; congruence).
    rewrite HReadMem2 by (left; destruct Hb; subst; congruence).
    rewrite HReadMem1 by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr3 b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm3. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr3 bd dbase bw outedge cursor 8).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write8_layout mr3 bd dbase bw outedge cursor
    (median8_payload (read8_result payload1) (read8_result payload2) (read8_result payload3)) HOutR)
    as (me & Hwrite & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm3. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_median8_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply byte_output_at_encode; [lia|].
        rewrite median8_decode, Hdecode1, Hdecode2, Hdecode3 in Houtput. exact Houtput.
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
           rewrite Hmemory; [|exact Hbd|].
           ++ rewrite HReadMem3 by (left; exact Hbl). rewrite HReadMem2 by (left; exact Hbl).
              rewrite HReadMem1 by (left; exact Hbl).
              erewrite Mem.load_storebytes_other; [|exact SC|auto].
              eapply Mem.load_alloc_unchanged; eauto.
           ++ rewrite byte_write_low_slice.
              pose proof (slice_write_low_bound 8 outedge cursor ltac:(lia) ltac:(lia)).
              destruct Hbw as [Hbw|[Hbw|Hbw]]; [left|right; left|right; right]; auto; lia.
Qed.

Theorem median8_local_spec : jet_local_spec f_simplicity_median_8 (Ty.Prod Word8 (Ty.Prod Word8 Word8)) Word8
  (fun xyz => @median_word_spec 3 Alg.CoreFunSem xyz).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x [y z]] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize Word8)) with 8 in *.
  change (Z.of_nat (bitSize (Ty.Prod Word8 (Ty.Prod Word8 Word8)))) with 24 in Hmax.
  apply frame_input_word_triple_encode in Hin.
  change (frame_input_word_at m bi edge rc x /\ frame_input_word_at m bi edge (rc + 8) y /\
    frame_input_word_at m bi edge (rc + 16) z) in Hin.
  destruct Hin as [HX [HY HZ]]. eapply eval_median8_layout_matches_spec; eauto.
  all: apply byte_slice_at_encode; split; [lia|apply frame_input_word_at_encode; assumption].
Qed.

Theorem median8_context : jet_context_for median8 (@median_word_spec 3).
Proof.
  exact (jet_context _ _ (median_word_spec_parametric 3) (median8_local_spec) ltac:(vm_compute; lia)).
Qed.
Definition median8_guarantees := jet_local_spec_guarantees _ _ _ _ (median8_local_spec).
Definition median8_context_guarantees :=
  jet_context_guarantees _ _ (median_word_spec_parametric 3) (median8_local_spec) ltac:(vm_compute; lia).

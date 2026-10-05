(** Input and output steps of the Bitcoin jets in the SHA translation unit:
    the readN / writeBit / skipBits / writeN calls, obtained from the verified
    core contracts by transport.  Ported from [jet_bitcoin_steps] and
    [jet_bitcoin_read_step]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_frame_spec C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_writeBit_layout_total C.jet_skipBits_layout C.jet_write_wide_layout_total.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_input_layout C.jet_complement_wide_layout.
Require C.jets.
Require Import C.jet_sha_linkage C.jet_sha_transport C.jet_bitcoin_effects.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque sha_ge ge0.
Set Default Timeout 60.

Lemma shx_writeBit_step m bf base bw edge cursor (bit : bool) :
  write_frame_at m bf base bw edge cursor 1 ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal jets.f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)]
      E0 mf (Vint (if bit then Int.one else Int.zero)) /\
    write_effect m mf bf base bw edge cursor 1 [Some bit].
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_writeBit_layout m bf base bw edge cursor bit HF)
    as (mf & w & HCall & HLoad & HBit & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - eapply sha_transport_call; [|exact HCall].
    unfold sha_core_helpers. simpl. tauto.
  - split.
    + intros i c Hi. destruct i as [|i]; [|destruct i; discriminate].
      simpl in Hi. injection Hi as Hc. subst c. cbn [cell_matches].
      split; [lia|]. exists w. split.
      * replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. exact HLoad.
      * replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. symmetry. exact HBit.
    + split; [exact HPrefix|]. split.
      * replace (cursor - 1) with (cursor - 1) by lia. exact HFields.
      * split; [|split; assumption].
        replace (edge + 8 * ((cursor - 1) / 64)) with (write_word_address edge cursor)
          by (unfold write_word_address; reflexivity).
        exact HLoads.
Qed.

Lemma shx_skipBits_step m bf base bw edge cursor n :
  write_frame_at m bf base bw edge cursor (Z.of_nat n) ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal jets.f_skipBits)
      [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat n))] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor (Z.of_nat n) (repeat None n).
Proof.
  intros HF.
  destruct (eval_skipBits_padding m bf base bw edge cursor n HF)
    as (mf & HCall & HCells & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - eapply sha_transport_call; [|exact HCall].
    unfold sha_core_helpers. simpl. tauto.
  - split; [exact HCells|]. split; [exact HPrefix|]. split; [exact HFields|].
    split; [|split; assumption].
    intros chunk b ofs H1 _. apply HLoads; exact H1.
Qed.

Lemma wide_writer_helper s : exists id, In (id, wide_writer s) sha_core_helpers.
Proof.
  destruct s; [exists jets._simplicity_write16|exists jets._simplicity_write32|exists jets._simplicity_write64];
    unfold sha_core_helpers, wide_writer; simpl; tauto.
Qed.

Lemma shx_write_wide_step s m bf base bw edge cursor x :
  write_frame_at m bf base bw edge cursor (wide_bits s) ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor (wide_bits s)
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x))).
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write_wide_layout s m bf base bw edge cursor x HF)
    as (mf & HCall & HSlice & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - destruct (wide_writer_helper s) as [id Hin]. eapply sha_transport_call; eauto.
  - split.
    + apply (wide_output_at_encode s); [lia|].
      exists (Int64.zero_ext (wide_bits s) x). split; [exact HSlice|reflexivity].
    + split; [exact HPrefix|]. split; [exact HFields|].
      split; [|split; assumption].
      intros chunk b ofs H1 H2. apply HLoads; [exact H1|].
      pose proof (slice_write_low_bound (wide_bits s) edge cursor (wide_bits_bounds s) ltac:(lia)) as HB.
      destruct H2 as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H].
Qed.

Lemma wide_reader_helper s : exists id, In (id, wide_reader s) sha_core_helpers.
Proof.
  destruct s; [exists jets._simplicity_read16|exists jets._simplicity_read32|exists jets._simplicity_read64];
    unfold sha_core_helpers, wide_reader; simpl; tauto.
Qed.

Lemma shx_read_wide_step s m ma mc bl bs sbase bi edge rc (x : Ty.tySem (Word (wide_log s))) bytes :
  0 <= rc <= Int64.max_unsigned - wide_bits s ->
  frame_fields_at m bs sbase bi edge rc ->
  frame_input_word_at m bi edge rc x ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  exists mr r,
    Clight2.eval_funcall sha_ge mc (Internal (wide_reader s)) [Vptr bl (Ptrofs.repr 0)] E0 mr (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ (wide_log s)) x /\
    frame_fields_at mr bl 0 bi edge (rc + wide_bits s) /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk mc b ofs) /\
    (forall b ofs kind p, Mem.perm mc b ofs kind p -> Mem.perm mr b ofs kind p) /\
    (forall b, Mem.valid_block mc b -> Mem.valid_block mr b) /\
    (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
Proof.
  intros HRC HF HIn HA HB SC.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct HF as [HSE HSO].
  destruct (wide_input_first_load s m bi edge rc x HIn) as [w Hw].
  assert (HLi : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa) as [HLE HLO].
  assert (HBefore : forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v).
  { intros chunk b ofs v HL.
    assert (Hbl : bl <> b) by (eapply fresh_frame_not_loaded; eauto).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (HInputC : frame_input_word_at mc bi edge rc x).
  { eapply frame_input_bits_at_preserved; [|exact HIn].
    intros ofs w' HL. apply HBefore; exact HL. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|].
    exists 1; reflexivity. }
  destruct (eval_read_wide_word_at s mc bl 0 bi edge rc x HLocalBase HRC (conj HLE HLO) HInputC PLC HLi)
    as (mr & r & Hread & Hr & HFields & HMem & HPerm & HValid).
  exists mr, r. split.
  - destruct (wide_reader_helper s) as [id Hin].
    eapply sha_transport_call; eauto.
  - split; [exact Hr|]. split; [exact HFields|]. split.
    + intros chunk b ofs Hb. apply HMem. left; exact Hb.
    + split; [exact HPerm|]. split; [exact HValid|].
      intros chunk b ofs v HL. rewrite HMem by (left; intro Heq; subst; eapply fresh_frame_not_loaded; eauto).
      apply HBefore; exact HL.
Qed.

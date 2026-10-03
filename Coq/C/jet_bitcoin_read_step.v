(** The first step of every indexed Bitcoin getter: [simplicity_readN(&src)] on
    the local by-value copy of the source frame, derived from the initial input
    cells and transported from the core environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_input_layout C.jet_wide C.jet_complement_wide_layout.
Require C.jets.
Require Import C.jet_bitcoin_linkage C.jet_bitcoin_transport.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Lemma wide_reader_helper s : exists id, In (id, wide_reader s) bitcoin_core_helpers.
Proof.
  destruct s; [exists jets._simplicity_read16|exists jets._simplicity_read32|exists jets._simplicity_read64];
    unfold bitcoin_core_helpers, wide_reader; simpl; tauto.
Qed.

Lemma bitcoin_read_wide_step s m ma mc bl bs sbase bi edge rc (x : Ty.tySem (Word (wide_log s))) bytes :
  0 <= rc <= Int64.max_unsigned - wide_bits s ->
  frame_fields_at m bs sbase bi edge rc ->
  frame_input_word_at m bi edge rc x ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  exists mr r,
    Clight2.eval_funcall bitcoin_ge mc (Internal (wide_reader s)) [Vptr bl (Ptrofs.repr 0)] E0 mr (Vlong r) /\
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
    eapply bitcoin_transport_call; eauto.
  - split; [exact Hr|]. split; [exact HFields|]. split.
    + intros chunk b ofs Hb. apply HMem. left; exact Hb.
    + split; [exact HPerm|]. split; [exact HValid|].
      intros chunk b ofs v HL. rewrite HMem by (left; intro Heq; subst; eapply fresh_frame_not_loaded; eauto).
      apply HBefore; exact HL.
Qed.

(** Layout contract of the context reader in the SHA translation unit:
    the proof of [jet_read_sha256_context_layout.v] with the sub-calls
    transported and the body composed in the SHA global environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout.
Require Import C.jet_read_sha256_prefix_layout C.jet_read32s_layout C.jet_word32_chunks.
Require Import C.jet_uint32_array_init.
Require Import C.jet_read_sha256_context_exec C.jet_read_sha256_counter C.jet_read_sha256_overflow.
Require Import C.jet_sha256_read_local C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_read_sha256_context_layout.
Require Import C.jet_sha_linkage C.jet_sha_transport C.jet_sha_read_context_exec.

Lemma sg_in_read_buffer8 : In (jets._simplicity_read_buffer8, jets.f_simplicity_read_buffer8) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.
Lemma sg_in_read64 : In (jets._simplicity_read64, jets.f_simplicity_read64) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.
Lemma sg_in_read32s : In (jets._read32s, jets.f_read32s) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.

Theorem sg_eval_read_sha256_context_allocated_layout m ma bf base bi edge cursor bc cbase bl bo output
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (state : Ty.tySem (Word 8)) :
  Mem.alloc m 0 8 = (ma,bl) ->
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.range_perm ma bc (cbase + 16) (cbase + 79) Cur Writable ->
  Mem.valid_access ma Mint64 bc (cbase + 8) Writable ->
  Mem.valid_access ma Mint8unsigned bc (cbase + 80) Writable ->
  Mem.load Mptr ma bc cbase = Some (Vptr bo (Ptrofs.repr output)) ->
  0 <= output -> output + 32 <= Ptrofs.max_unsigned -> (4 | output) ->
  Mem.range_perm ma bo output (output + 32) Cur Writable ->
  bf <> bc -> bf <> bi -> bc <> bi -> bl <> bf -> bl <> bc -> bl <> bi ->
  bo <> bf -> bo <> bi -> bo <> bc -> bl <> bo ->
  bf <> sha_symbol_block _sha256_max_counter -> bc <> sha_symbol_block _sha256_max_counter ->
  bl <> sha_symbol_block _sha256_max_counter -> bo <> sha_symbol_block _sha256_max_counter ->
  Mem.load Mint64 ma (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  frame_base_valid base -> 0 <= cursor -> cursor + 830 <= Int64.max_unsigned ->
  frame_fields_at ma bf base bi edge cursor -> Mem.valid_access ma Mint64 bf (base + 8) Writable ->
  frame_input_cells_at ma bi edge cursor (encode buf ++ encode count ++ encode state) ->
  exists mf r,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_read_sha256_context)
      [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] E0 mf
      (Vint (bit_int (negb (sha256_read_overflow r)))) /\
    Int64.unsigned r = @toZ (WordToZ 6) count /\
    Mem.load Mptr mf bc cbase = Some (Vptr bo (Ptrofs.repr output)) /\
    uint8_array_at mf bc (cbase + 16)
      (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf))) /\
    uint32_array_at mf bo output (map word32_array_value (word32_chunks 3 state)) /\
    Mem.load Mint64 mf bc (cbase + 8) = Some (Vlong (sha256_read_counter r (Int64.repr
      (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))))) /\
    Mem.load Mint8unsigned mf bc (cbase + 80) = Some (Vint (bit_int (sha256_read_overflow r))) /\
    frame_fields_at mf bf base bi edge (cursor + 830) /\
    Mem.load Mint64 mf (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) /\
    (forall b ofs kind p, b <> bl -> Mem.perm ma b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall chunk b ofs, b <> bl ->
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bc \/ ofs + size_chunk chunk <= cbase + 8 \/ cbase + 81 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 32 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk ma b ofs).
Proof.
  intros HA HB HM HBufP HCtxW HOverW HOutput HO HOM HOA HOutP
    Hfc Hfi Hci Hlf Hlc Hli Hof Hoi Hoc Hlo Hfg Hcg Hlg Hog HGlobal
    Hbase HC HMax HF HW HCells.
  assert (HFree : Mem.range_perm ma bl 0 8 Cur Freeable).
  { intros ofs HR. eapply Mem.perm_alloc_2; eauto. }
  assert (HLenW : Mem.valid_access ma Mint64 bl 0 Writable).
  { split; [intros ofs HR; eapply Mem.perm_implies; [apply HFree; exact HR|constructor]|exists 0; reflexivity]. }
  destruct (read_sha256_prefix_layout ma bf base bi edge cursor bc cbase bl buf count state
    HB HM HBufP HCtxW HLenW Hfc Hfi Hci Hlf Hlc Hli Hbase HC HMax HF HW HCells)
    as (mb & mc & md & r & HBuffer & HRead & Hr & HLen & HCounter & HArray & HFd & HState & HMemP & HPermP & HValidP).
  assert (HOutputD : Mem.load Mptr md bc cbase = Some (Vptr bo (Ptrofs.repr output))).
  { rewrite HMemP; [exact HOutput|left; congruence|right; left; change (size_chunk Mptr) with 8; lia|left; congruence]. }
  assert (HOutPD : Mem.range_perm md bo output (output + 32) Cur Writable).
  { intros ofs HR; apply HPermP, HOutP; exact HR. }
  assert (HWd : Mem.valid_access md Mint64 bf (base + 8) Writable).
  { destruct HW as [HP HAlign]. split; [intros ofs HR; apply HPermP, HP; exact HR|exact HAlign]. }
  assert (HChunks : length (word32_chunks 3 state) = 8%nat) by apply word32_chunks_length.
  destruct (eval_read32s_layout md bo output bf base bi edge (cursor + 574) (word32_chunks 3 state)
    HO ltac:(rewrite HChunks; exact HOM) HOA ltac:(rewrite HChunks; exact HOutPD)
    ltac:(congruence) Hfi Hoi Hbase ltac:(lia)
    ltac:(rewrite HChunks; change (cursor + 574 + 256 <= Int64.max_unsigned); lia) HFd HWd
    (frame_input_word32_chunks md bi edge (cursor + 574) 3 state HState))
    as (me & HReadState & HStateArray & HFe & HMemS & HPermS & HValidS).
  rewrite HChunks in HReadState, HFe, HMemS.
  change (frame_fields_at me bf base bi edge (cursor + 574 + 256)) in HFe.
  assert (HGlobalE : Mem.load Mint64 me (sha_symbol_block _sha256_max_counter) 0 =
    Some (Vlong (Int64.repr 2305843009213693952))).
  { rewrite HMemS by (left; congruence). rewrite HMemP by (left; congruence); exact HGlobal. }
  assert (HOverWE : Mem.valid_access me Mint8unsigned bc (cbase + 80) Writable).
  { destruct HOverW as [HP HAlign]. split; [intros ofs HR; apply HPermS, HPermP, HP; exact HR|exact HAlign]. }
  assert (HFreeE : Mem.range_perm me bl 0 8 Cur Freeable).
  { intros ofs HR; apply HPermS, HPermP, HFree; exact HR. }
  rewrite <- (sha256_context_block_pointer cbase HB HM) in HBuffer.
  apply (sha_transport_call _ _ sg_in_read_buffer8) in HBuffer.
  apply (sha_transport_call _ _ sg_in_read64) in HRead.
  apply (sha_transport_call _ _ sg_in_read32s) in HReadState.
  destruct (sg_eval_sha256_read_context_composes m ma mb mc md me bl bc cbase bf base bo output r
    (Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf)))))
    HB HM HA HBuffer HRead HLen HCounter HOutputD HReadState HGlobalE Hcg HOverWE HFreeE)
    as (mx & mf & HCall & HOverStore & HFreeCall & HMemFree & HPermFree & HNext).
  assert (HCounterX : Mem.load Mint64 mx bc (cbase + 8) = Some (Vlong (sha256_read_counter r (Int64.repr
    (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf)))))))).
  { erewrite Mem.load_store_other; [|exact HOverStore|right; left; change (size_chunk Mint64) with 8; lia].
    rewrite HMemS by (left; congruence). rewrite (Mem.load_store_same _ _ _ _ _ _ HCounter); reflexivity. }
  assert (HOverX : Mem.load Mint8unsigned mx bc (cbase + 80) = Some (Vint (bit_int (sha256_read_overflow r)))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ HOverStore); destruct (sha256_read_overflow r); reflexivity. }
  assert (HFieldsX : frame_fields_at mx bf base bi edge (cursor + 830)).
  { replace (cursor + 830) with (cursor + 574 + 256) by lia.
    destruct HFe as [HEdge HCursor]. split;
      erewrite Mem.load_store_other; [exact HEdge|exact HOverStore|left; congruence|
        exact HCursor|exact HOverStore|left; congruence]. }
  assert (HBound : (length (byte_chunks_values (buffer_byte_chunks 5 buf)) <= 63)%nat).
  { pose proof (byte_chunks_values_bound _ (buffer_byte_chunks_sized 5 buf)) as H.
    rewrite buffer63_chunks_capacity in H; exact H. }
  assert (HArrayF : uint8_array_at mf bc (cbase + 16)
    (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf)))).
  { intros i x HX.
    assert (HI : (i < length (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf))))%nat).
    { apply nth_error_Some; rewrite HX; discriminate. }
    rewrite map_length in HI. rewrite HMemFree by congruence.
    erewrite Mem.load_store_other; [|exact HOverStore|right; left; change (size_chunk Mint8unsigned) with 1; lia].
    rewrite HMemS by (left; congruence). apply HArray; exact HX.
  }
  exists mf, r. split; [exact HCall|]. split; [exact Hr|]. split.
  - rewrite HMemFree by congruence.
    erewrite Mem.load_store_other; [|exact HOverStore|right; left; change (size_chunk Mptr) with 8; lia].
    rewrite HMemS by (left; congruence); exact HOutputD.
  - split; [exact HArrayF|]. split.
    + intros i x HX. rewrite HMemFree by congruence.
    erewrite Mem.load_store_other; [apply HStateArray; exact HX|exact HOverStore|left; congruence].
    + split; [rewrite HMemFree by congruence; exact HCounterX|].
    split; [rewrite HMemFree by congruence; exact HOverX|]. split.
      * destruct HFieldsX as [HEdge HCursor]. split; rewrite HMemFree by congruence; assumption.
      * split.
        -- rewrite HMemFree by congruence.
        erewrite Mem.load_store_other; [exact HGlobalE|exact HOverStore|left; congruence].
        -- split.
           ++ intros b ofs kind p HOther HP. apply HPermFree; [exact HOther|].
              eapply Mem.perm_store_1; [exact HOverStore|apply HPermS, HPermP; exact HP].
           ++ intros chunk b ofs Hbl Hbf Hbc Hbo.
              rewrite HMemFree by exact Hbl.
              erewrite Mem.load_store_other; [|exact HOverStore|].
              ** rewrite HMemS by assumption. apply HMemP; [exact Hbf| |left; congruence].
                 destruct Hbc as [HN|[HL|HH]]; [left; exact HN|right; left; exact HL|right; right; lia].
              ** change (b <> bc \/ ofs + size_chunk chunk <= cbase + 80 \/ cbase + 80 + 1 <= ofs).
                 destruct Hbc as [HN|[HL|HH]]; [left; exact HN|right; left; lia|right; right; lia].
Qed.

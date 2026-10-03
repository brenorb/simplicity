(** Total actual context serialization from initial canonical buffer/state
    observations, including either overflow return. Shared representation
    infrastructure, not an individual public jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_output_sequence_step C.jet_encoding C.jet_bitmachine_rep C.jet_word_repr.
Require Import C.jet_uint32_array_init C.jet_read32s_layout C.jet_write32s_layout C.jet_word32_chunks.
Require Import C.jet_wide C.jet_wide_spec C.jet_readBit_layout C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks.
Require Import C.jet_read8s_layout C.jet_write_buffer8_layout C.jet_write64_then32s_layout C.jet_write_sha256_context_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma word32_array_decode x :
  @fromZ (WordToZ 5) (Int.unsigned (word32_array_value x)) = x.
Proof.
  pose proof (word_toZ_range 5 x) as HR.
  change (0 <= @toZ (WordToZ 5) x < 4294967296) in HR.
  unfold word32_array_value. rewrite Int.unsigned_repr by (change (0 <= @toZ (WordToZ 5) x <= 4294967295); lia).
  apply from_toZ.
Qed.
Lemma uint32_word_cells_encode xs :
  uint32_word_cells (map word32_array_value xs) = concat (map (@encode (Word 5)) xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (encode (@fromZ (WordToZ 5) (Int.unsigned (word32_array_value x))) ++
    uint32_word_cells (map word32_array_value xs) = encode x ++ concat (map (@encode (Word 5)) xs)).
  rewrite word32_array_decode, IH; reflexivity.
Qed.

Theorem eval_write_sha256_context_layout m bf base bw edge cursor bc cbase bi input counter overflow
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (state : Ty.tySem (Word 8)) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= input -> input + 32 <= Ptrofs.max_unsigned ->
  bc <> bf -> bc <> bw -> bi <> bf -> bi <> bw ->
  Mem.load Mint64 m bc (cbase + 8) = Some (Vlong counter) ->
  Mem.load Mptr m bc cbase = Some (Vptr bi (Ptrofs.repr input)) ->
  Mem.load Mint8unsigned m bc (cbase + 80) = Some (Vint (bit_int overflow)) ->
  uint8_array_at m bc (cbase + 16) (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf))) ->
  Int64.modu counter (Int64.repr 64) = Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf)))) ->
  uint32_array_at m bi input (map word32_array_value (word32_chunks 3 state)) ->
  write_frame_at m bf base bw edge cursor 830 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write_sha256_context)
      [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.repr cbase)] E0 mf (Vint (bit_int (negb overflow))) /\
    frame_output_cells_at mf bw edge cursor
      (@encode (Ty.Prod (buffer_type (Word 3) 5) (Ty.Prod (Word 6) (Word 8)))
        (buf, (decode_wide W64 (Int64.zero_ext 64 (Int64.shru counter (Int64.repr 6))), state))) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 830) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 830) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HM HI HIM Hcf Hcw Hif Hiw HC HO HF HBuf HLen HA HW.
  pose proof HW as [_ [_ [_ [HCurs [_ [Hfw _]]]]]].
  assert (HStateLength : length (map word32_array_value (word32_chunks 3 state)) = 8%nat).
  { rewrite map_length, word32_chunks_length; reflexivity. }
  assert (HAddr : Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16) = Ptrofs.repr (cbase + 16)).
  { unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16; reflexivity. }
  destruct (eval_write_buffer8_layout m bc (cbase + 16) bf base bw edge cursor 320 buf
    ltac:(lia) ltac:(lia) ltac:(lia) Hcf Hcw HBuf HW)
    as (mb & HBuffer & HCells & HPrefix & HWNext & HMem & HPerm & HValid).
  rewrite <- HAddr, <- HLen in HBuffer.
  assert (HCb : Mem.load Mint64 mb bc (cbase + 8) = Some (Vlong counter)).
  { rewrite HMem by (left; assumption); exact HC. }
  assert (HAb : uint32_array_at mb bi input (map word32_array_value (word32_chunks 3 state))).
  { intros i v Hv; rewrite HMem by (left; assumption); exact (HA i v Hv). }
  destruct (eval_write64_then32s_layout mb bi input bf base bw edge (cursor - 510)
    (Int64.shru counter (Int64.repr 6)) (map word32_array_value (word32_chunks 3 state))
    HI ltac:(rewrite HStateLength; exact HIM) Hif Hiw HAb ltac:(rewrite HStateLength; exact HWNext))
    as (mc & mf & HCounter & HState & HTail & HPrefixTail & HFieldsTail & HMem64 & HMemTail & HPermTail & HValidTail).
  rewrite HStateLength in HState, HFieldsTail, HMemTail.
  change (frame_fields_at mf bf base bw edge (cursor - 510 - 320)) in HFieldsTail.
  change (loads_outside_ranges mb mf bf (base + 8) (base + 16)
    bw (edge + 8 * ((cursor - 510 - 320) / 64)) (write_word_address edge (cursor - 510) + 8)) in HMemTail.
  assert (HOc : Mem.load Mptr mc bc cbase = Some (Vptr bi (Ptrofs.repr input))).
  { rewrite HMem64 by (left; assumption); rewrite HMem by (left; assumption); exact HO. }
  assert (HFf : Mem.load Mint8unsigned mf bc (cbase + 80) = Some (Vint (bit_int overflow))).
  { rewrite HMemTail by (left; assumption); rewrite HMem by (left; assumption); exact HF. }
  assert (HBufLength : Z.of_nat (length (encode buf)) = 510).
  { rewrite buffer_byte_chunks_cells, byte_chunks_cells_width by apply buffer_byte_chunks_sized.
    apply buffer63_chunks_width. }
  assert (HFirstFinal : frame_output_cells_at mf bw edge cursor (encode buf)).
  { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base) (cursor := cursor - 510);
      [exact Hfw|rewrite HBufLength; lia|exact HPrefixTail|exact HMemTail|exact HCells]. }
  assert (HLo : edge + 8 * ((cursor - 830) / 64) <= edge + 8 * ((cursor - 510) / 64)).
  { pose proof (Z.div_le_mono (cursor - 830) (cursor - 510) 64 ltac:(lia) ltac:(lia)); lia. }
  assert (HPrev : write_word_address edge (cursor - 510) <= write_word_address edge cursor).
  { unfold write_word_address. pose proof (Z.div_le_mono (cursor - 510 - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
  exists mf. split.
  - eapply eval_write_sha256_context_composes; eauto.
  - split.
    + change (frame_output_cells_at mf bw edge cursor
        (encode buf ++ (encode (decode_wide W64 (Int64.zero_ext 64 (Int64.shru counter (Int64.repr 6)))) ++ encode state))).
      apply frame_output_cells_at_app; split; [exact HFirstFinal|]. rewrite HBufLength.
      rewrite uint32_word_cells_encode, <- word32_chunks_encode in HTail; exact HTail.
    + split.
      * eapply write_prefix_at_chain with (next := cursor - 510);
          [exact Hfw|lia|exact HPrefix|exact HPrefixTail|exact HMemTail].
      * split.
        -- replace (cursor - 830) with (cursor - 510 - 320) by lia; exact HFieldsTail.
        -- split.
           ++ intros chunk b ofs Hbf Hbw; rewrite HMemTail.
              ** apply HMem; [exact Hbf|]. destruct Hbw as [N|[L|R]]; auto; right; lia.
              ** exact Hbf.
              ** replace (cursor - 510 - 320) with (cursor - 830) by lia.
                 destruct Hbw as [N|[L|R]]; auto; right; lia.
           ++ split; [intros; apply HPermTail, HPerm; assumption|intros; apply HValidTail, HValid; assumption].
Qed.

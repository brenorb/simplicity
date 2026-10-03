(** Derive the buffer/count reads and counter store from initial encoded cells.
    The private length slot is supplied by actual function-entry allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout.
Require Import C.jet_read_buffer8_layout C.jet_read64_input_word_total C.jet_read_sha256_counter.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem read_sha256_prefix_layout m bf base bi edge cursor bc cbase bl
    (buf : Ty.tySem (buffer_type (Word 3) 5))
    (count : Ty.tySem (Word 6)) (state : Ty.tySem (Word 8)) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bc (cbase + 16) (cbase + 79) Cur Writable ->
  Mem.valid_access m Mint64 bc (cbase + 8) Writable ->
  Mem.valid_access m Mint64 bl 0 Writable ->
  bf <> bc -> bf <> bi -> bc <> bi -> bl <> bf -> bl <> bc -> bl <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 830 <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (encode buf ++ encode count ++ encode state) ->
  exists mb mc md r,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
      [Vptr bc (Ptrofs.repr (cbase + 16)); Vptr bl Ptrofs.zero;
        Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef /\
    Clight2.eval_funcall ge0 mb (Internal f_simplicity_read64)
      [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ 6) count /\
    Mem.load Mint64 mc bl 0 = Some (Vlong (Int64.repr
      (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf)))))) /\
    Mem.store Mint64 mc bc (cbase + 8)
      (Vlong (sha256_read_counter r (Int64.repr
        (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))))) = Some md /\
    uint8_array_at md bc (cbase + 16)
      (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf))) /\
    frame_fields_at md bf base bi edge (cursor + 574) /\
    frame_input_cells_at md bi edge (cursor + 574) (encode state) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bc \/ ofs + size_chunk chunk <= cbase + 8 \/ cbase + 79 <= ofs) ->
      (b <> bl \/ ofs + size_chunk chunk <= 0 \/ 8 <= ofs) ->
      Mem.load chunk md b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm md b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block md b).
Proof.
  intros HB HM HBufP HCtxW HLenW Hfc Hfi Hci Hlf Hlc Hli Hbase HC HMax HF HW HCells.
  assert (HBufLength : Z.of_nat (length (encode buf)) = 510).
  { rewrite buffer_byte_chunks_cells, byte_chunks_cells_width by apply buffer_byte_chunks_sized.
    apply buffer63_chunks_width. }
  apply frame_input_cells_at_app in HCells. destruct HCells as [HBuf HRest].
  rewrite HBufLength in HRest. apply frame_input_cells_at_app in HRest.
  destruct HRest as [HCount HState]. rewrite encode_word_length in HState.
  change (frame_input_cells_at m bi edge (cursor + 510 + 64) (encode state)) in HState.
  destruct (eval_read_buffer8_layout m bf base bi edge cursor bc (cbase + 16) bl 0 buf
    ltac:(lia) ltac:(lia) ltac:(replace (cbase + 16 + 63) with (cbase + 79) by lia; exact HBufP)
    ltac:(change (0 <= 0 <= 18446744073709551615); lia) HLenW Hfc Hfi Hci Hlf Hlc Hli
    Hbase HC ltac:(lia) HF HW HBuf)
    as (mb & HBuffer & HArray & HLen & HFb & HMemB & HPermB & HValidB).
  assert (HCountB : frame_input_word_at mb bi edge (cursor + 510) count).
  { apply frame_input_word_at_encode.
    eapply buffer_input_cells_preserved; [|exact HCount].
    intros ofs w HL. rewrite HMemB by (left; congruence); exact HL. }
  assert (HWb : Mem.valid_access mb Mint64 bf (base + 8) Writable).
  { destruct HW as [HP HA]. split; [intros ofs HR; apply HPermB, HP; exact HR|exact HA]. }
  destruct (eval_read64_word_at mb bf base bi edge (cursor + 510) count Hbase ltac:(lia) HFb HCountB HWb Hfi)
    as (mc & r & HRead & Hr & HFc & HMemC & HPermC & HValidC).
  assert (HLenC : Mem.load Mint64 mc bl 0 = Some (Vlong (Int64.repr
    (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))))).
  { rewrite HMemC by (left; congruence); exact HLen. }
  assert (HCtxWC : Mem.valid_access mc Mint64 bc (cbase + 8) Writable).
  { destruct HCtxW as [HP HA]. split; [intros ofs HR; apply HPermC, HPermB, HP; exact HR|exact HA]. }
  destruct (Mem.valid_access_store mc Mint64 bc (cbase + 8)
    (Vlong (sha256_read_counter r (Int64.repr
      (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))))) HCtxWC) as [md HS].
  assert (HFields : frame_fields_at md bf base bi edge (cursor + 574)).
  { replace (cursor + 574) with (cursor + 510 + 64) by lia.
    destruct HFc as [HE HCc]. split;
      erewrite Mem.load_store_other; [exact HE|exact HS|left; congruence|
        exact HCc|exact HS|left; congruence]. }
  assert (HMemory : forall chunk b ofs,
    (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
    (b <> bc \/ ofs + size_chunk chunk <= cbase + 8 \/ cbase + 79 <= ofs) ->
    (b <> bl \/ ofs + size_chunk chunk <= 0 \/ 8 <= ofs) ->
    Mem.load chunk md b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hbf Hbc Hbl.
    erewrite Mem.load_store_other; [|exact HS|].
    - rewrite HMemC by exact Hbf. apply HMemB; [exact Hbf| |exact Hbl].
      destruct Hbc as [HN|[HL|HH]]; [left; exact HN|right; left; lia|right; right; lia].
    - change (b <> bc \/ ofs + size_chunk chunk <= cbase + 8 \/ cbase + 8 + 8 <= ofs).
      destruct Hbc as [HN|[HL|HH]]; auto; right; right; lia. }
  assert (HArrayD : uint8_array_at md bc (cbase + 16)
    (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf)))).
  { intros i x HX. erewrite Mem.load_store_other; [|exact HS|right; right; change (size_chunk Mint64) with 8; lia].
    rewrite HMemC by (left; congruence). apply HArray; exact HX. }
  assert (HStateD : frame_input_cells_at md bi edge (cursor + 574) (encode state)).
  { eapply buffer_input_cells_preserved.
    - intros ofs w HL. rewrite HMemory by (left; congruence); exact HL.
    - replace (cursor + 574) with (cursor + 510 + 64) by lia; exact HState. }
  exists mb, mc, md, r. split; [exact HBuffer|]. split; [exact HRead|].
  split; [exact Hr|]. split; [exact HLenC|]. split; [exact HS|].
  split; [exact HArrayD|]. split; [exact HFields|]. split; [exact HStateD|].
  split; [exact HMemory|]. split.
  - intros b ofs kind p HP. eapply Mem.perm_store_1; [exact HS|apply HPermC, HPermB; exact HP].
  - intros b HV. eapply Mem.store_valid_block_1; [exact HS|apply HValidC, HValidB; exact HV].
Qed.

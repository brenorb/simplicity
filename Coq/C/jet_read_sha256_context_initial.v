(** Complete context-reader helper from initial memory, with actual allocation.
    Canonical public jet callers and program bridges remain separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout.
Require Import C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require Import C.jet_read_sha256_context_layout C.jet_read_sha256_counter C.jet_read_sha256_overflow.
Require Import C.jet_sha256_read_local C.jet_sha256_max_counter C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma frame_input_word_valid_block n m bi edge cursor (x : Ty.tySem (Word n)) :
  frame_input_word_at m bi edge cursor x -> Mem.valid_block m bi.
Proof.
  intro HInput.
  destruct (nth_error (frame_input_word_bits x) 0) as [b|] eqn:HL.
  - destruct (HInput 0%nat b HL) as [_ [_ [w [HLoad _]]]].
    eapply Mem.perm_valid_block.
    eapply (Mem.valid_access_perm m Mint64 _ _ Cur Readable).
    eapply Mem.load_valid_access; exact HLoad.
  - apply nth_error_None in HL. rewrite frame_input_word_bits_length in HL.
    pose proof (Nat.pow_nonzero 2 n ltac:(discriminate)); lia.
Qed.

Theorem eval_read_sha256_context_initial_layout m bf base bi edge cursor bc cbase bo output
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (state : Ty.tySem (Word 8)) :
  sha256_max_counter_at m ->
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bc (cbase + 16) (cbase + 79) Cur Writable ->
  Mem.valid_access m Mint64 bc (cbase + 8) Writable ->
  Mem.valid_access m Mint8unsigned bc (cbase + 80) Writable ->
  Mem.load Mptr m bc cbase = Some (Vptr bo (Ptrofs.repr output)) ->
  0 <= output -> output + 32 <= Ptrofs.max_unsigned -> (4 | output) ->
  Mem.range_perm m bo output (output + 32) Cur Writable ->
  bf <> bc -> bf <> bi -> bc <> bi -> bo <> bf -> bo <> bi -> bo <> bc ->
  frame_base_valid base -> 0 <= cursor -> cursor + 830 <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (encode buf ++ encode count ++ encode state) ->
  exists mf r,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_sha256_context)
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
    Mem.load Mint64 mf (jet_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bc \/ ofs + size_chunk chunk <= cbase + 8 \/ cbase + 81 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 32 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HGlobal HB HM HBufP HCtxW HOverW HOutput HO HOM HOA HOutP
    Hfc Hfi Hci Hof Hoi Hoc Hbase HC HMax HF HW HCells.
  assert (Vf : Mem.valid_block m bf).
  { eapply Mem.perm_valid_block. eapply (Mem.valid_access_perm m Mint64 _ _ Cur Writable); exact HW. }
  assert (Vc : Mem.valid_block m bc).
  { eapply Mem.perm_valid_block. eapply (Mem.valid_access_perm m Mint64 _ _ Cur Writable); exact HCtxW. }
  assert (Vo : Mem.valid_block m bo).
  { eapply Mem.perm_valid_block. apply (HOutP output); lia. }
  assert (Vi : Mem.valid_block m bi).
  { apply frame_input_cells_at_app in HCells as [_ HRest].
    apply frame_input_cells_at_app in HRest as [HCount _].
    eapply frame_input_word_valid_block. apply frame_input_word_at_encode; exact HCount. }
  assert (Hfg : bf <> jet_symbol_block _sha256_max_counter)
    by (eapply sha256_max_counter_writable_other; eauto).
  assert (Hcg : bc <> jet_symbol_block _sha256_max_counter)
    by (eapply sha256_max_counter_writable_other; eauto).
  assert (Hog : bo <> jet_symbol_block _sha256_max_counter).
  { intro HE; subst bo. apply (proj2 HGlobal output); apply HOutP; lia. }
  destruct (allocate_sha256_read_local m bc cbase bf base HGlobal)
    as (ma & bl & HA & HEntry & HFree & HLenW & HOther & HMemA & HPermA & HGlobalA).
  assert (Hlf : bl <> bf) by (pose proof (HOther bf Vf); congruence).
  assert (Hlc : bl <> bc) by (pose proof (HOther bc Vc); congruence).
  assert (Hli : bl <> bi) by (pose proof (HOther bi Vi); congruence).
  assert (Hlo : bl <> bo) by (pose proof (HOther bo Vo); congruence).
  assert (Hlg : bl <> jet_symbol_block _sha256_max_counter).
  { pose proof (HOther _ (sha256_max_counter_valid_block m HGlobal)); congruence. }
  assert (HBufPA : Mem.range_perm ma bc (cbase + 16) (cbase + 79) Cur Writable).
  { intros ofs HR; apply HPermA, HBufP; exact HR. }
  assert (HOutPA : Mem.range_perm ma bo output (output + 32) Cur Writable).
  { intros ofs HR; apply HPermA, HOutP; exact HR. }
  assert (HCtxWA : Mem.valid_access ma Mint64 bc (cbase + 8) Writable).
  { eapply Mem.valid_access_alloc_other; eauto. }
  assert (HOverWA : Mem.valid_access ma Mint8unsigned bc (cbase + 80) Writable).
  { eapply Mem.valid_access_alloc_other; eauto. }
  assert (HWA : Mem.valid_access ma Mint64 bf (base + 8) Writable).
  { eapply Mem.valid_access_alloc_other; eauto. }
  assert (HOutputA : Mem.load Mptr ma bc cbase = Some (Vptr bo (Ptrofs.repr output))).
  { rewrite HMemA by exact Vc; exact HOutput. }
  assert (HFA : frame_fields_at ma bf base bi edge cursor).
  { destruct HF as [HE HCursor]. split; rewrite HMemA by exact Vf; assumption. }
  assert (HCellsA : frame_input_cells_at ma bi edge cursor (encode buf ++ encode count ++ encode state)).
  { eapply buffer_input_cells_preserved; [|exact HCells].
    intros ofs w HL; rewrite HMemA by exact Vi; exact HL. }
  destruct (eval_read_sha256_context_allocated_layout m ma bf base bi edge cursor bc cbase bl bo output buf count state
    HA HB HM HBufPA HCtxWA HOverWA HOutputA HO HOM HOA HOutPA
    Hfc Hfi Hci Hlf Hlc Hli Hof Hoi Hoc Hlo Hfg Hcg Hlg Hog (proj1 HGlobalA)
    Hbase HC HMax HFA HWA HCellsA)
    as (mf & r & HCall & Hr & HOutputF & HArray & HState & HCounter & HOver & HFields & HLimit & HPermF & HMemF).
  exists mf, r. do 9 (split; [assumption|]). split.
  - intros b ofs kind p HP. apply HPermF.
    + pose proof (HOther b (Mem.perm_valid_block _ _ _ _ _ HP)); congruence.
    + apply HPermA; exact HP.
  - intros chunk b ofs HV Hbf Hbc Hbo.
    rewrite HMemF by (first [assumption|pose proof (HOther b HV); congruence]).
    apply HMemA; exact HV.
Qed.

(** Actual complete context-reader call with its return interpreted through the
    literal canonical compression-count assertion. This is a helper contract,
    not a complete public add/finalize jet specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout.
Require Import C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init C.jet_partial.
Require Import C.jet_read_sha256_context_initial C.jet_read_sha256_counter C.jet_read_sha256_overflow.
Require Import C.jet_sha256_max_counter C.jet_readBit_layout C.jet_sha256_count_assertion.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_read_sha256_context_count_contract m bf base bi edge cursor bc cbase bo output
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
      (jet_partial_return (@sha256_count_assertion_spec (Alg.AssertionSem option_Monad_Zero) (buf,(count,state)))) /\
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
  destruct (eval_read_sha256_context_initial_layout m bf base bi edge cursor bc cbase bo output buf count state
    HGlobal HB HM HBufP HCtxW HOverW HOutput HO HOM HOA HOutP Hfc Hfi Hci Hof Hoi Hoc Hbase HC HMax HF HW HCells)
    as (mf & r & HCall & Hr & HOutputF & HArray & HState & HCounter & HOver & HFields & HLimit & HPerm & HMem).
  exists mf, r. split.
  - replace (@sha256_count_assertion_spec (Alg.AssertionSem option_Monad_Zero) (buf,(count,state))) with
      (if negb (sha256_read_overflow r) then Some tt else None) by
      (symmetry; exact (sha256_read_return_matches_count_assertion buf count state r Hr)).
    unfold jet_partial_return. destruct (negb (sha256_read_overflow r)); exact HCall.
  - do 9 (split; [assumption|]); exact HMem.
Qed.

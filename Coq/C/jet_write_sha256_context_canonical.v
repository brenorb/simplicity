(** Specialize the actual writer to the counter reconstructed by the reader.
    Quotient/remainder and output decoding are derived, not preconditions.
    This is serializer support, not an individual public jet proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_uint32_array_init C.jet_word32_chunks.
Require Import C.jet_readBit_layout C.jet_read_sha256_counter C.jet_sha256_counter_representation.
Require Import C.jet_write_sha256_context_layout.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma sha256_count_carrier_decode r (count : Ty.tySem (Word 6)) :
  Int64.unsigned r = @toZ (WordToZ 6) count ->
  decode_wide W64 (Int64.zero_ext 64 r) = count.
Proof.
  intro Hr. rewrite Int64.zero_ext_above by (change Int64.zwordsize with 64; lia).
  change (@fromZ (WordToZ 6) (Int64.unsigned r) = count).
  rewrite Hr; apply from_toZ.
Qed.

Lemma sha256_reader_counter_decode r (count : Ty.tySem (Word 6))
    (buf : Ty.tySem (buffer_type (Word 3) 5)) :
  Int64.unsigned r = @toZ (WordToZ 6) count ->
  @toZ (WordToZ 6) count < 36028797018963968 ->
  decode_wide W64 (Int64.zero_ext 64
    (Int64.shru (sha256_read_counter r (Int64.repr
      (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf)))))) (Int64.repr 6))) = count.
Proof.
  intros Hr HC.
  destruct (sha256_counter_buffer63_representation r buf ltac:(rewrite Hr; exact HC))
    as [_ [_ HQ]].
  rewrite HQ. apply sha256_count_carrier_decode; exact Hr.
Qed.

Theorem eval_write_sha256_context_canonical m bf base bw edge cursor bc cbase bi input r overflow
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (state : Ty.tySem (Word 8)) :
  Int64.unsigned r = @toZ (WordToZ 6) count ->
  @toZ (WordToZ 6) count < 36028797018963968 ->
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= input -> input + 32 <= Ptrofs.max_unsigned ->
  bc <> bf -> bc <> bw -> bi <> bf -> bi <> bw ->
  Mem.load Mint64 m bc (cbase + 8) = Some (Vlong (sha256_read_counter r (Int64.repr
    (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))))) ->
  Mem.load Mptr m bc cbase = Some (Vptr bi (Ptrofs.repr input)) ->
  Mem.load Mint8unsigned m bc (cbase + 80) = Some (Vint (bit_int overflow)) ->
  uint8_array_at m bc (cbase + 16) (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf))) ->
  uint32_array_at m bi input (map word32_array_value (word32_chunks 3 state)) ->
  write_frame_at m bf base bw edge cursor 830 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write_sha256_context)
      [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.repr cbase)] E0 mf (Vint (bit_int (negb overflow))) /\
    frame_output_cells_at mf bw edge cursor
      (@encode (Ty.Prod (buffer_type (Word 3) 5) (Ty.Prod (Word 6) (Word 8))) (buf,(count,state))) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 830) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 830) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Hr HCount HB HM HI HIM Hcf Hcw Hif Hiw HC HO HF HBuf HA HW.
  destruct (sha256_counter_buffer63_representation r buf ltac:(rewrite Hr; exact HCount))
    as [_ [HLen _]].
  destruct (eval_write_sha256_context_layout m bf base bw edge cursor bc cbase bi input
    (sha256_read_counter r (Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))))
    overflow buf state HB HM HI HIM Hcf Hcw Hif Hiw HC HO HF HBuf HLen HA HW)
    as (mf & HCall & HCells & HPrefix & HFields & HMem & HPerm & HValid).
  rewrite (sha256_reader_counter_decode r count buf Hr HCount) in HCells.
  exists mf. split; [exact HCall|]. split; [exact HCells|].
  do 4 (split; [assumption|]); exact HValid.
Qed.

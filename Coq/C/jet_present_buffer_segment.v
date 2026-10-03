(** Total actual true-tag and byte-array payload from initial memory. Retains
    exact canonical cells, previous contents and writable continuation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_output_sequence_step C.jet_output_cells_step.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_writeBit_layout_total.
Require Import C.jet_buffer_chunks C.jet_read8s_layout C.jet_write8s_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_present_buffer_segment m bi input bf base bw edge cursor xs tail :
  (0 < length xs)%nat -> 0 <= tail ->
  0 <= input -> input + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  bi <> bf -> bi <> bw -> uint8_array_at m bi input (map word8_array_value xs) ->
  write_frame_at m bf base bw edge cursor (1 + 8 * Z.of_nat (length xs) + tail) ->
  exists mb mf,
    Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint Int.one] E0 mb (Vint Int.one) /\
    Clight2.eval_funcall ge0 mb (Internal f_write8s)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input);
        Vlong (Int64.repr (Z.of_nat (length xs)))] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (Some Datatypes.true :: concat (map (@encode (Word 3)) xs)) /\
    write_prefix_at m mf bw edge cursor /\
    write_frame_at mf bf base bw edge (cursor - (1 + 8 * Z.of_nat (length xs))) tail /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - (1 + 8 * Z.of_nat (length xs))) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HN HT HI HM Hif Hiw HA HFrame.
  pose proof HFrame as [HB [HF [HE [HC [HMax [HD [PD HW]]]]]]].
  assert (Hone : write_frame_at m bf base bw edge cursor 1)
    by (eapply write_frame_at_shorter; [|exact HFrame]; lia).
  destruct (eval_writeBit_layout m bf base bw edge cursor Datatypes.true Hone)
    as (mb & bitword & HBit & HBitLoad & HBitValue & HBitPrefix & HBitFields & HBitMem & HBitPerm & HBitValid).
  assert (Hnext : write_frame_at mb bf base bw edge (cursor - 1) (8 * Z.of_nat (length xs) + tail)).
  { eapply write_frame_at_after_bit with (w := bitword); [lia| |exact HBitFields|exact HBitLoad|exact HBitMem|exact HBitPerm].
    replace (8 * Z.of_nat (length xs) + tail + 1) with (1 + 8 * Z.of_nat (length xs) + tail) by lia.
    exact HFrame. }
  assert (HArrayNext : uint8_array_at mb bi input (map word8_array_value xs)).
  { intros i x Hx; rewrite HBitMem by (left; assumption); exact (HA i x Hx). }
  assert (HPayload : write_frame_at mb bf base bw edge (cursor - 1) (8 * Z.of_nat (length xs)))
    by (eapply write_frame_at_shorter; [|exact Hnext]; lia).
  destruct (eval_write8s_words_layout mb bi input bf base bw edge (cursor - 1) xs
    HI HM Hif Hiw HArrayNext HPayload)
    as (mf & HBytes & HCells & HBytePrefix & HByteFields & HByteMem & HBytePerm & HByteValid).
  assert (HTail : write_frame_at mf bf base bw edge (cursor - (1 + 8 * Z.of_nat (length xs))) tail).
  { replace (cursor - (1 + 8 * Z.of_nat (length xs))) with (cursor - 1 - 8 * Z.of_nat (length xs)) by lia.
    replace (8 * Z.of_nat (length xs)) with
      (Z.of_nat (length (concat (map (@encode (Word 3)) xs))))
      by (rewrite encoded_byte_list_length, Nat2Z.inj_mul; reflexivity).
    eapply write_frame_at_after_cells with (m := mb) (cursor := cursor - 1)
      (cells := concat (map (@encode (Word 3)) xs)).
    - rewrite encoded_byte_list_length; lia.
    - exact HT.
    - rewrite encoded_byte_list_length, Nat2Z.inj_mul. change (Z.of_nat 8) with 8; exact Hnext.
    - rewrite encoded_byte_list_length, Nat2Z.inj_mul. change (Z.of_nat 8) with 8; exact HByteFields.
    - exact HCells.
    - rewrite encoded_byte_list_length, Nat2Z.inj_mul. change (Z.of_nat 8) with 8; exact HByteMem.
    - exact HBytePerm. }
  assert (HFirst : frame_output_cells_at mb bw edge cursor [Some Datatypes.true]).
  { intros [|[|i]] c Hi; cbn in Hi; try discriminate. injection Hi as <-.
    cbn [cell_matches]. split; [lia|]. exists bitword.
    replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. split; [exact HBitLoad|].
    symmetry; exact HBitValue. }
  assert (HFirstFinal : frame_output_cells_at mf bw edge cursor [Some Datatypes.true]).
  { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base) (cursor := cursor - 1);
      [exact HD|cbn [length]; lia|exact HBytePrefix|exact HByteMem|exact HFirst]. }
  exists mb, mf. split; [exact HBit|]. split; [exact HBytes|]. split.
  - change (frame_output_cells_at mf bw edge cursor ([Some Datatypes.true] ++ concat (map (@encode (Word 3)) xs))).
    apply frame_output_cells_at_app; split; [exact HFirstFinal|exact HCells].
  - split.
    + eapply write_prefix_at_chain with (next := cursor - 1);
        [exact HD|lia|exact HBitPrefix|exact HBytePrefix|exact HByteMem].
    + split; [exact HTail|]. split.
      * intros chunk b ofs Hbf Hbw. rewrite HByteMem.
        -- apply HBitMem; [exact Hbf|].
           assert (HLow : edge + 8 * ((cursor - (1 + 8 * Z.of_nat (length xs))) / 64) <= write_word_address edge cursor).
           { unfold write_word_address. pose proof (Z.div_le_mono
               (cursor - (1 + 8 * Z.of_nat (length xs))) (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
           destruct Hbw as [N|[L|R]]; [left; exact N|right; left; lia|right; right; exact R].
        -- exact Hbf.
        -- replace (cursor - 1 - 8 * Z.of_nat (length xs)) with
             (cursor - (1 + 8 * Z.of_nat (length xs))) by lia.
           destruct Hbw as [N|[L|R]]; [left; exact N|right; left; exact L|right; right].
           unfold write_word_address in R |- *.
           pose proof (Z.div_le_mono (cursor - 1 - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia.
      * split; [intros; apply HBytePerm, HBitPerm; assumption|intros; apply HByteValid, HBitValid; assumption].
Qed.

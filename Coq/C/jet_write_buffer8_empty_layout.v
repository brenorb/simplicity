(** Initial-only memory consumer of the actual empty-buffer writer. All
    writeBit/skipBits calls are derived, with arbitrary padding contents. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_output_sequence_step.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_empty_buffer_segment.
Require Import C.jet_buffer_empty_spec.
Require Import C.jet_write_buffer8_empty_run C.jet_write_buffer8_empty_call C.jet_write_buffer8_empty_cells.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem buffer8_empty_calls_layout m bf base bw edge cursor xs tail :
  0 <= tail -> buffer8_empty_chain xs ->
  write_frame_at m bf base bw edge cursor (buffer8_empty_bits xs + tail) ->
  exists mf,
    buffer8_empty_calls bf base xs m mf /\
    frame_output_cells_at mf bw edge cursor (buffer8_empty_output_cells xs) /\
    write_prefix_at m mf bw edge cursor /\
    write_frame_at mf bf base bw edge (cursor - buffer8_empty_bits xs) tail /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - buffer8_empty_bits xs) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Htail. revert m cursor. induction xs as [|j xs IH]; intros m cursor Hchain HW.
  - exists m. split; [reflexivity|]. split.
    + intros i c Hi. destruct i; discriminate.
    + split.
      * intros old HL. exists old. split; [exact HL|].
        unfold word_outside_eq; intros; reflexivity.
      * split.
        -- change (write_frame_at m bf base bw edge (cursor - 0) tail).
           rewrite Z.sub_0_r. exact HW.
        -- split; [unfold loads_outside_ranges; intros; reflexivity|]. split; auto.
  - destruct Hchain as [HJ [Hhalf Hchain]].
    pose proof (buffer8_empty_bits_nonnegative xs Hchain) as HtailBits.
    pose proof HW as [HFBase [HFields [HE [HC [HMax [Hfw [PW HWords]]]]]]].
    set (width := 1 + 8 * j).
    assert (Hcount : Z.of_nat (Z.to_nat (8 * j)) = 8 * j) by (apply Z2Nat.id; lia).
    assert (HSegment : write_frame_at m bf base bw edge cursor
      (1 + Z.of_nat (Z.to_nat (8 * j)) + (buffer8_empty_bits xs + tail))).
    { rewrite Hcount. replace (1 + 8 * j + (buffer8_empty_bits xs + tail)) with
        (buffer8_empty_bits (j :: xs) + tail) by (cbn [buffer8_empty_bits]; ring). exact HW. }
    destruct (eval_empty_buffer_segment m bf base bw edge cursor (Z.to_nat (8 * j))
      (buffer8_empty_bits xs + tail) ltac:(lia) HSegment)
      as (mb & mi & HBit & HSkip & HHead & HPrefix & HWNext & HMem & HPerm & HValid).
    rewrite Hcount in HSkip, HWNext, HMem.
    change (loads_outside_ranges m mi bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - width) / 64)) (write_word_address edge cursor + 8)) in HMem.
    change (write_frame_at mi bf base bw edge (cursor - width) (buffer8_empty_bits xs + tail)) in HWNext.
    destruct (IH mi (cursor - width) Hchain HWNext)
      as (mf & HRun & HTail & HPrefixTail & HFieldsTail & HMemTail & HPermTail & HValidTail).
    assert (HHeadLength : Z.of_nat (@length BitMachine.Cell
      (Some Datatypes.false :: repeat None (Z.to_nat (8 * j)))) = width).
    { cbn [length]. rewrite repeat_length, Nat2Z.inj_succ, Hcount. unfold width; lia. }
    assert (HfirstFinal : frame_output_cells_at mf bw edge cursor
      (Some Datatypes.false :: repeat None (Z.to_nat (8 * j)))).
    { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
        (cursor := cursor - width); [exact Hfw| |exact HPrefixTail|exact HMemTail|exact HHead].
      rewrite HHeadLength. cbn [buffer8_empty_bits] in HC. unfold width; lia. }
    assert (HLo : edge + 8 * ((cursor - buffer8_empty_bits (j :: xs)) / 64) <=
      edge + 8 * ((cursor - width) / 64)).
    { pose proof (Z.div_le_mono (cursor - buffer8_empty_bits (j :: xs)) (cursor - width) 64
        ltac:(lia) ltac:(cbn [buffer8_empty_bits]; unfold width; lia)). nia. }
    assert (HPrev : write_word_address edge (cursor - width) <= write_word_address edge cursor).
    { unfold write_word_address. pose proof (Z.div_le_mono (cursor - width - 1) (cursor - 1) 64
        ltac:(lia) ltac:(unfold width; lia)); nia. }
    exists mf. split.
    + exists mb, mi. split; [exact HBit|]. split; [exact HSkip|exact HRun].
    + split.
      * change (frame_output_cells_at mf bw edge cursor
          ((Some Datatypes.false :: repeat None (Z.to_nat (8 * j))) ++ buffer8_empty_output_cells xs)).
        apply frame_output_cells_at_app. split; [exact HfirstFinal|]. rewrite HHeadLength. exact HTail.
      * split.
        -- eapply write_prefix_at_chain; [exact Hfw| |exact HPrefix|exact HPrefixTail|exact HMemTail].
           cbn [buffer8_empty_bits] in HC. unfold width; lia.
        -- split.
           ++ change (write_frame_at mf bf base bw edge (cursor - (1 + 8 * j + buffer8_empty_bits xs)) tail).
              replace (cursor - (1 + 8 * j + buffer8_empty_bits xs)) with
                (cursor - width - buffer8_empty_bits xs) by (unfold width; ring). exact HFieldsTail.
           ++ split.
              ** intros chunk b ofs Hbf Hbw. rewrite HMemTail.
                 --- apply HMem; [exact Hbf|].
                     destruct Hbw as [Hneq|[Hbefore|Hafter]];
                       [left|right; left|right; right]; auto; nia.
                 --- exact Hbf.
                 --- replace (cursor - width - buffer8_empty_bits xs) with
                       (cursor - buffer8_empty_bits (j :: xs)) by (cbn [buffer8_empty_bits]; unfold width; ring).
                     destruct Hbw as [Hneq|[Hbefore|Hafter]];
                       [left|right; left|right; right]; auto; nia.
              ** split.
                 --- intros b ofs kind p HP. apply HPermTail, HPerm; exact HP.
                 --- intros b HV. apply HValidTail, HValid; exact HV.
Qed.

Theorem eval_write_buffer8_empty_layout m bf base bw edge cursor buf :
  write_frame_at m bf base bw edge cursor 510 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
      [Vptr bf (Ptrofs.repr base); buf; Vlong Int64.zero; Vint (Int.repr 5)] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (buffer_empty_cells (Word 3) 5) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 510) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 510) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HW. destruct (buffer8_empty_calls_layout m bf base bw edge cursor buffer63_empty_counts 0
    ltac:(lia) buffer63_empty_counts_chain ltac:(rewrite Z.add_0_r; exact HW))
    as (mf & HRun & HCells & HPrefix & HFields & HMem & HPerm & HValid).
  exists mf. split; [apply eval_write_buffer8_empty_composes; exact HRun|].
  rewrite buffer63_empty_output_canonical in HCells. exact (conj HCells
    (conj HPrefix (conj (proj1 (proj2 HFields)) (conj HMem (conj HPerm HValid))))).
Qed.

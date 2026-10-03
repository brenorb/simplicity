(** Total actual mixed-buffer writer loop. All tag decisions and branch calls
    follow from canonical chunk sizes and initial arrays/frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_output_sequence_step C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_buffer_input C.jet_buffer_chunks C.jet_buffer_write_choices C.jet_read8s_layout.
Require Import C.jet_write_buffer8_empty_exec C.jet_write_buffer8_empty_run C.jet_write_buffer8_exec.
Require Import C.jet_write_buffer8_chunk_layout C.jet_read_buffer8_loop_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_buffer8_write_loop_layout chunks m le bi input bf base bw edge cursor tail :
  byte_chunks_sized chunks -> byte_chunks_ordered chunks ->
  buffer8_empty_chain (map (fun c => Z.of_nat (fst c)) chunks) ->
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) -> le!_buf = Some (Vptr bi (Ptrofs.repr input)) ->
  le!_len = Some (Vlong (Int64.repr (Z.of_nat (length (byte_chunks_values chunks))))) ->
  le!_i = Some (Vlong (Int64.repr (buffer8_empty_index (map (fun c => Z.of_nat (fst c)) chunks)))) ->
  0 <= tail -> 0 <= input -> input + Z.of_nat (byte_chunks_capacity chunks) <= Ptrofs.max_unsigned ->
  Z.of_nat (byte_chunks_capacity chunks) <= Int64.max_unsigned -> bi <> bf -> bi <> bw ->
  uint8_array_at m bi input (map word8_array_value (byte_chunks_values chunks)) ->
  write_frame_at m bf base bw edge cursor (byte_chunks_width chunks + tail) ->
  exists mf lef,
    Clight2.exec_stmt ge0 empty_env le m buffer8_actual_loop E0 lef mf Out_normal /\
    frame_output_cells_at mf bw edge cursor (concat (map byte_chunk_cells chunks)) /\
    write_prefix_at m mf bw edge cursor /\
    write_frame_at mf bf base bw edge (cursor - byte_chunks_width chunks) tail /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - byte_chunks_width chunks) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HSized HOrdered HChain. revert m le input cursor.
  induction chunks as [|c cs IH]; intros m le input cursor HD HB HL HI HT HInput HMax HCap Hif Hiw HA HW.
  - exists m, le. split; [apply exec_buffer8_empty_stop; exact HI|]. split.
    + intros i c Hi; destruct i; discriminate.
    + split.
      * intros old HLoad; exists old; split; [exact HLoad|]. unfold word_outside_eq; intros; reflexivity.
      * split; [rewrite Z.sub_0_r; exact HW|].
        split; [unfold loads_outside_ranges; intros; reflexivity|]. split; auto.
  - inversion HSized as [|c' cs' HCSize HCSized]; subst c' cs'.
    change ((byte_chunks_capacity cs < fst c)%nat /\ byte_chunks_ordered cs) in HOrdered.
    destruct HOrdered as [HSmall HOrder].
    change (0 < Z.of_nat (fst c) <= Int64.max_unsigned /\
      Z.of_nat (fst c) / 2 = buffer8_empty_index (map (fun c => Z.of_nat (fst c)) cs) /\
      buffer8_empty_chain (map (fun c => Z.of_nat (fst c)) cs)) in HChain.
    destruct HChain as [HJ [Hhalf HChain]].
    assert (HCapacity : Z.of_nat (byte_chunks_capacity (c :: cs)) =
      Z.of_nat (fst c) + Z.of_nat (byte_chunks_capacity cs)).
    { cbn [byte_chunks_capacity]; rewrite Nat2Z.inj_add; reflexivity. }
    rewrite HCapacity in HMax, HCap.
    pose proof (byte_chunks_width_nonnegative cs) as HTWidth.
    pose proof (byte_chunks_values_bound (c :: cs) HSized) as HValueBound.
    assert (HLength : Z.of_nat (length (byte_chunks_values (c :: cs))) =
      Z.of_nat (length (byte_chunk_values c)) + Z.of_nat (length (byte_chunks_values cs))).
    { cbn [byte_chunks_values]; rewrite app_length, Nat2Z.inj_add; reflexivity. }
    change (uint8_array_at m bi input (map word8_array_value (byte_chunk_values c ++ byte_chunks_values cs))) in HA.
    rewrite map_app in HA. apply uint8_array_at_app in HA. rewrite map_length in HA.
    destruct HA as [HAHead HATail].
    pose proof HW as [_ [_ [_ [HFrameCount [HCursor [Hfw _]]]]]].
    destruct (exec_buffer8_write_chunk_layout m le bi input bf base bw edge cursor
      (Z.of_nat (length (byte_chunks_values (c :: cs)))) c (byte_chunks_width cs + tail)
      HD HB HL HI ltac:(lia) HCSize ltac:(cbn [byte_chunks_capacity] in HValueBound; lia)
      (byte_chunk_remaining_choice c cs HCSize HCSized HSmall) ltac:(lia) HInput ltac:(lia) Hif Hiw HAHead
      ltac:(cbn [byte_chunks_width] in HW; replace (1 + 8 * Z.of_nat (fst c) + (byte_chunks_width cs + tail))
        with (1 + 8 * Z.of_nat (fst c) + byte_chunks_width cs + tail) by lia; exact HW))
      as (ms & HStep & HHead & HPrefix & HWNext & HMemory & HPerm & HValid).
    set (next := PTree.set _i (Vlong (Int64.repr (Z.of_nat (fst c) / 2)))
      (buffer8_write_chunk_temps le bi input (Z.of_nat (length (byte_chunks_values (c :: cs)))) c)).
    assert (HANext : uint8_array_at ms bi (input + Z.of_nat (length (byte_chunk_values c)))
      (map word8_array_value (byte_chunks_values cs))).
    { intros i x Hx; rewrite HMemory by (left; assumption); exact (HATail i x Hx). }
    destruct (IH HCSized HOrder HChain ms next (input + Z.of_nat (length (byte_chunk_values c)))
      (cursor - (1 + 8 * Z.of_nat (fst c)))
      ltac:(unfold next; rewrite PTree.gso by discriminate; rewrite buffer8_write_chunk_dst; exact HD)
      ltac:(unfold next; rewrite PTree.gso by discriminate; apply buffer8_write_chunk_buf; assumption)
      ltac:(unfold next; rewrite PTree.gso by discriminate; rewrite buffer8_write_chunk_len by assumption;
        rewrite HLength; replace (Z.of_nat (length (byte_chunk_values c)) + Z.of_nat (length (byte_chunks_values cs)) -
          Z.of_nat (length (byte_chunk_values c))) with (Z.of_nat (length (byte_chunks_values cs))) by lia; reflexivity)
      ltac:(unfold next; rewrite PTree.gss, Hhalf; reflexivity) HT ltac:(lia)
      ltac:(pose proof (byte_chunk_values_bound c HCSize); lia) ltac:(lia) Hif Hiw HANext HWNext)
      as (mf & lef & HRest & HTailCells & HPrefixTail & HFrameTail & HMemoryTail & HPermTail & HValidTail).
    assert (HHeadFinal : frame_output_cells_at mf bw edge cursor (byte_chunk_cells c)).
    { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
        (cursor := cursor - (1 + 8 * Z.of_nat (fst c)));
        [exact Hfw| |exact HPrefixTail|exact HMemoryTail|exact HHead].
      rewrite byte_chunk_cells_width by exact HCSize.
      cbn [byte_chunks_width] in HFrameCount; lia. }
    assert (HLo : edge + 8 * ((cursor - byte_chunks_width (c :: cs)) / 64) <=
      edge + 8 * ((cursor - (1 + 8 * Z.of_nat (fst c))) / 64)).
    { pose proof (Z.div_le_mono (cursor - byte_chunks_width (c :: cs))
        (cursor - (1 + 8 * Z.of_nat (fst c))) 64 ltac:(lia) ltac:(cbn [byte_chunks_width]; lia)); lia. }
    assert (HPrev : write_word_address edge (cursor - (1 + 8 * Z.of_nat (fst c))) <= write_word_address edge cursor).
    { unfold write_word_address. pose proof (Z.div_le_mono
        (cursor - (1 + 8 * Z.of_nat (fst c)) - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
    exists mf, lef. split.
    + unfold buffer8_loop_body, buffer8_loop_update in HStep.
      rewrite buffer8_actual_loop_shape in HStep, HRest |- *.
      eapply empty_loop_from_normal_sequence; [exact HStep|exact HRest].
    + split.
      * change (frame_output_cells_at mf bw edge cursor (byte_chunk_cells c ++ concat (map byte_chunk_cells cs))).
        apply frame_output_cells_at_app. split; [exact HHeadFinal|].
        rewrite byte_chunk_cells_width by exact HCSize; exact HTailCells.
      * split.
        -- eapply write_prefix_at_chain with (next := cursor - (1 + 8 * Z.of_nat (fst c)));
             [exact Hfw|cbn [byte_chunks_width] in HFrameCount; lia|exact HPrefix|exact HPrefixTail|exact HMemoryTail].
        -- split.
           ++ replace (cursor - byte_chunks_width (c :: cs)) with
                (cursor - (1 + 8 * Z.of_nat (fst c)) - byte_chunks_width cs) by (cbn [byte_chunks_width]; lia).
              exact HFrameTail.
           ++ split.
              ** intros chunk b ofs Hbf Hbw. rewrite HMemoryTail.
                 --- apply HMemory; [exact Hbf|]. destruct Hbw as [N|[L|R]]; auto; right; lia.
                 --- exact Hbf.
                 --- replace (cursor - (1 + 8 * Z.of_nat (fst c)) - byte_chunks_width cs) with
                       (cursor - byte_chunks_width (c :: cs)) by (cbn [byte_chunks_width]; lia).
                     destruct Hbw as [N|[L|R]]; auto; right; lia.
              ** split; [intros; apply HPermTail, HPerm; assumption|intros; apply HValidTail, HValid; assumption].
Qed.

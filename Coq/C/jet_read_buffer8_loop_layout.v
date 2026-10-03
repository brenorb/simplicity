(** Total actual mixed-buffer loop, consuming canonical cells and producing
    exactly its present bytes. No intermediate call/store execution is assumed.
    Entry/length initialization and individual public jets are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_input_layout C.jet_frame_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout C.jet_read_buffer8_exec.
Require Import C.jet_read_buffer8_chunk_layout C.jet_write_buffer8_empty_run.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma byte_chunks_width_nonnegative cs : 0 <= byte_chunks_width cs.
Proof.
  induction cs as [|c cs IH]; [cbn [byte_chunks_width]; lia|].
  cbn [byte_chunks_width]. pose proof (Nat2Z.is_nonneg (fst c)); lia.
Qed.

Theorem exec_buffer8_read_loop_layout chunks m le bf base bi edge cursor bo output bl slot count :
  byte_chunks_sized chunks -> buffer8_empty_chain (map (fun c => Z.of_nat (fst c)) chunks) ->
  le!_src = Some (Vptr bf (Ptrofs.repr base)) -> le!_buf = Some (Vptr bo (Ptrofs.repr output)) ->
  le!_len = Some (Vptr bl (Ptrofs.repr slot)) ->
  le!_i = Some (Vlong (Int64.repr (buffer8_empty_index (map (fun c => Z.of_nat (fst c)) chunks)))) ->
  0 <= output -> output + Z.of_nat (byte_chunks_capacity chunks) <= Ptrofs.max_unsigned ->
  0 <= slot <= Ptrofs.max_unsigned -> 0 <= count -> count + Z.of_nat (byte_chunks_capacity chunks) <= Int64.max_unsigned ->
  Mem.range_perm m bo output (output + Z.of_nat (byte_chunks_capacity chunks)) Cur Writable ->
  Mem.valid_access m Mint64 bl slot Writable -> Mem.load Mint64 m bl slot = Some (Vlong (Int64.repr count)) ->
  bf <> bo -> bf <> bi -> bo <> bi -> bl <> bf -> bl <> bo -> bl <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + byte_chunks_width chunks <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (concat (map byte_chunk_cells chunks)) ->
  exists mf lef,
    Clight2.exec_stmt ge0 empty_env le m buffer8_read_loop E0 lef mf Out_normal /\
    uint8_array_at mf bo output (map word8_array_value (byte_chunks_values chunks)) /\
    Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr (count + Z.of_nat (length (byte_chunks_values chunks))))) /\
    frame_fields_at mf bf base bi edge (cursor + byte_chunks_width chunks) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + Z.of_nat (byte_chunks_capacity chunks) <= ofs) ->
      (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  revert m le cursor output count. induction chunks as [|c cs IH]; intros m le cursor output count
    HSized HChain HS HB HL HI HO HM Hslot HC HCount HP HWLen HLoad Hfo Hfi Hoi Hlf Hlo Hli Hbase HCursor HMax HF HW HCells.
  - exists m, le. split; [apply exec_buffer8_read_stop; exact HI|]. split.
    + intros i x Hx; destruct i; discriminate.
    + split; [rewrite Z.add_0_r; exact HLoad|]. split; [rewrite Z.add_0_r; exact HF|].
      split; [intros; reflexivity|]. split; auto.
  - inversion HSized as [|c' cs' HCSize HCSized]; subst c' cs'.
    change (0 < Z.of_nat (fst c) <= Int64.max_unsigned /\
      Z.of_nat (fst c) / 2 = buffer8_empty_index (map (fun c => Z.of_nat (fst c)) cs) /\
      buffer8_empty_chain (map (fun c => Z.of_nat (fst c)) cs)) in HChain.
    destruct HChain as [HJ [Hhalf HChain]].
    assert (HCapacity : Z.of_nat (byte_chunks_capacity (c :: cs)) =
      Z.of_nat (fst c) + Z.of_nat (byte_chunks_capacity cs)).
    { cbn [byte_chunks_capacity]. rewrite Nat2Z.inj_add; reflexivity. }
    rewrite HCapacity in HM, HCount, HP.
    pose proof (byte_chunks_width_nonnegative cs) as HTWidth.
    pose proof (byte_chunk_values_bound c HCSize) as HHeadBound.
    change (frame_input_cells_at m bi edge cursor (byte_chunk_cells c ++ concat (map byte_chunk_cells cs))) in HCells.
    apply frame_input_cells_at_app in HCells. destruct HCells as [HHead HTail].
    destruct (exec_buffer8_read_chunk_layout m le bf base bi edge cursor bo output bl slot count c
      HS HB HL HI ltac:(lia) HCSize HO ltac:(lia) Hslot HC ltac:(lia)
      ltac:(intros ofs HR; apply HP; lia) HWLen HLoad Hfo Hfi Hoi Hlf Hlo Hbase HCursor
      ltac:(cbn [byte_chunks_width] in HMax; lia) HF HW HHead)
      as (ms & HStep & HArray & HLen & HFields & HMemory & HPerm & HValid).
    set (next := PTree.set _i (Vlong (Int64.repr (Z.of_nat (fst c) / 2)))
      (buffer8_read_chunk_temps le bo output count c)).
    assert (HWNext : Mem.valid_access ms Mint64 bf (base + 8) Writable).
    { destruct HW as [HPermOld HA]. split; [|exact HA]. intros ofs HR; apply HPerm, HPermOld; exact HR. }
    assert (HWLenNext : Mem.valid_access ms Mint64 bl slot Writable).
    { destruct HWLen as [HPermOld HA]. split; [|exact HA]. intros ofs HR; apply HPerm, HPermOld; exact HR. }
    assert (HPNext : Mem.range_perm ms bo (output + Z.of_nat (length (byte_chunk_values c)))
      (output + Z.of_nat (length (byte_chunk_values c)) + Z.of_nat (byte_chunks_capacity cs)) Cur Writable).
    { intros ofs HR. apply HPerm, HP; lia. }
    assert (HInputNext : frame_input_cells_at ms bi edge (cursor + 1 + 8 * Z.of_nat (fst c))
      (concat (map byte_chunk_cells cs))).
    { eapply buffer_input_cells_preserved.
      - intros ofs w HLoadOld. rewrite HMemory; [exact HLoadOld|left; congruence|left; congruence|left; congruence].
      - rewrite (byte_chunk_cells_width c HCSize) in HTail.
        replace (cursor + 1 + 8 * Z.of_nat (fst c)) with (cursor + (1 + 8 * Z.of_nat (fst c))) by lia. exact HTail. }
    destruct (IH ms next (cursor + 1 + 8 * Z.of_nat (fst c))
      (output + Z.of_nat (length (byte_chunk_values c))) (count + Z.of_nat (length (byte_chunk_values c)))
      HCSized HChain
      ltac:(unfold next; rewrite PTree.gso by discriminate; rewrite buffer8_read_chunk_src; exact HS)
      ltac:(unfold next; rewrite PTree.gso by discriminate; apply buffer8_read_chunk_buf; exact HB)
      ltac:(unfold next; rewrite PTree.gso by discriminate; rewrite buffer8_read_chunk_len; exact HL)
      ltac:(unfold next; rewrite PTree.gss, Hhalf; reflexivity) ltac:(lia) ltac:(lia) Hslot ltac:(lia) ltac:(lia)
      HPNext HWLenNext HLen Hfo Hfi Hoi Hlf Hlo Hli Hbase ltac:(lia)
      ltac:(cbn [byte_chunks_width] in HMax; lia) HFields HWNext HInputNext)
      as (mf & lef & HRest & HTailArray & HLenFinal & HFieldsFinal & HMemoryFinal & HPermFinal & HValidFinal).
    assert (HHeadFinal : uint8_array_at mf bo output (map word8_array_value (byte_chunk_values c))).
    { eapply uint8_array_before_preserved with (m := ms)
        (next := output + Z.of_nat (length (byte_chunk_values c))); [rewrite map_length; lia| |exact HArray].
      intros ofs HBefore. apply HMemoryFinal; [left; congruence|right; left; exact HBefore|left; congruence]. }
    exists mf, lef. split.
    + unfold buffer8_read_body, buffer8_read_update in HStep.
      rewrite buffer8_read_loop_shape in HStep, HRest |- *.
      eapply empty_loop_from_normal_sequence; [exact HStep|exact HRest].
    + split.
      * change (uint8_array_at mf bo output (map word8_array_value (byte_chunk_values c ++ byte_chunks_values cs))).
        rewrite map_app. apply uint8_array_at_app. split; [exact HHeadFinal|]. rewrite map_length. exact HTailArray.
      * split.
        -- change (Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr
             (count + Z.of_nat (length (byte_chunk_values c ++ byte_chunks_values cs)))))).
           rewrite app_length, Nat2Z.inj_add. replace
             (count + (Z.of_nat (length (byte_chunk_values c)) + Z.of_nat (length (byte_chunks_values cs))))
             with (count + Z.of_nat (length (byte_chunk_values c)) + Z.of_nat (length (byte_chunks_values cs))) by lia.
           exact HLenFinal.
        -- split.
           ++ replace (cursor + byte_chunks_width (c :: cs)) with
                (cursor + 1 + 8 * Z.of_nat (fst c) + byte_chunks_width cs) by (cbn [byte_chunks_width]; lia).
              exact HFieldsFinal.
           ++ split.
              ** intros chunk b ofs Hbf Hbo Hbl. rewrite HMemoryFinal.
                 --- apply HMemory; [exact Hbf| |exact Hbl].
                     rewrite HCapacity in Hbo. destruct Hbo as [HN|[HBef|HAft]]; auto; right; lia.
                 --- exact Hbf.
                 --- rewrite HCapacity in Hbo. destruct Hbo as [HN|[HBef|HAft]]; auto; right; lia.
                 --- exact Hbl.
              ** split; [intros; apply HPermFinal, HPerm; assumption|intros; apply HValidFinal, HValid; assumption].
Qed.

(** Complete actual Buffer63 reader from initial canonical cells, including
    arbitrary absent/present mixtures, length initialization and normal return.
    This is shared implementation infrastructure, not individual jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout.
Require Import C.jet_read_buffer8_call C.jet_read_buffer8_loop_layout C.jet_write_buffer8_empty_run.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_read_buffer8_layout m bf base bi edge cursor bo output bl slot
    (x : Ty.tySem (buffer_type (Word 3) 5)) :
  0 <= output -> output + 63 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bo output (output + 63) Cur Writable ->
  0 <= slot <= Ptrofs.max_unsigned -> Mem.valid_access m Mint64 bl slot Writable ->
  bf <> bo -> bf <> bi -> bo <> bi -> bl <> bf -> bl <> bo -> bl <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 510 <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (encode x) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
      [Vptr bo (Ptrofs.repr output); Vptr bl (Ptrofs.repr slot); Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)]
      E0 mf Vundef /\
    uint8_array_at mf bo output (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 x))) /\
    Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 x)))))) /\
    frame_fields_at mf bf base bi edge (cursor + 510) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 63 <= ofs) ->
      (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HO HM HP Hslot HWLen Hfo Hfi Hoi Hlf Hlo Hli Hbase HC HMax HF HW HCells.
  destruct (Mem.valid_access_store m Mint64 bl slot (Vlong Int64.zero) HWLen) as [mz HStore].
  assert (HFz : frame_fields_at mz bf base bi edge cursor).
  { destruct HF as [HEdge HCursor]. split;
      erewrite Mem.load_store_other; [exact HEdge|exact HStore|left; congruence|
        exact HCursor|exact HStore|left; congruence]. }
  assert (HWz : Mem.valid_access mz Mint64 bf (base + 8) Writable) by (eapply Mem.store_valid_access_1; eauto).
  assert (HWLenz : Mem.valid_access mz Mint64 bl slot Writable) by (eapply Mem.store_valid_access_1; eauto).
  assert (HPz : Mem.range_perm mz bo output (output + 63) Cur Writable).
  { intros ofs HR. eapply Mem.perm_store_1; [exact HStore|apply HP; exact HR]. }
  assert (HCellsz : frame_input_cells_at mz bi edge cursor (concat (map byte_chunk_cells (buffer_byte_chunks 5 x)))).
  { rewrite <- buffer_byte_chunks_cells. eapply buffer_input_cells_preserved; [|exact HCells].
    intros ofs w HL. erewrite Mem.load_store_other; [exact HL|exact HStore|left; congruence]. }
  set (le := PTree.set _i (Vlong (Int64.repr 32)) (buffer8_read_temps bf base bo output bl slot)).
  assert (HI : le!_i = Some (Vlong (Int64.repr
    (buffer8_empty_index (map (fun c => Z.of_nat (fst c)) (buffer_byte_chunks 5 x)))))).
  { rewrite <- map_map, buffer_byte_chunks_counts. unfold le. apply PTree.gss. }
  destruct (exec_buffer8_read_loop_layout (buffer_byte_chunks 5 x) mz le bf base bi edge cursor bo output bl slot 0
    (buffer_byte_chunks_sized 5 x) (buffer63_chunks_chain x)
    ltac:(unfold le, buffer8_read_temps; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold le, buffer8_read_temps; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold le, buffer8_read_temps; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    HI HO ltac:(rewrite buffer63_chunks_capacity; exact HM) Hslot ltac:(lia)
    ltac:(rewrite buffer63_chunks_capacity; change (0 + 63 <= 18446744073709551615); lia)
    ltac:(rewrite buffer63_chunks_capacity; exact HPz) HWLenz
    (Mem.load_store_same _ _ _ _ _ _ HStore) Hfo Hfi Hoi Hlf Hlo Hli Hbase HC
    ltac:(rewrite buffer63_chunks_width; exact HMax) HFz HWz HCellsz)
    as (mf & lef & HLoop & HArray & HLen & HFields & HMemory & HPerm & HValid).
  rewrite buffer63_chunks_width in HFields. rewrite buffer63_chunks_capacity in HMemory.
  exists mf. split; [eapply eval_read_buffer8_from_loop; eauto|]. split; [exact HArray|].
  split; [rewrite Z.add_0_l in HLen; exact HLen|]. split; [exact HFields|]. split.
  - intros chunk b ofs Hbf Hbo Hbl. rewrite HMemory by assumption.
    eapply Mem.load_store_other; [exact HStore|].
    change (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs). exact Hbl.
  - split; [intros; apply HPerm; eapply Mem.perm_store_1; eauto|
      intros; apply HValid; eapply Mem.store_valid_block_1; eauto].
Qed.

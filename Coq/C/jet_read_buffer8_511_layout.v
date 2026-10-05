(** The Buffer511 instance (n = 8) of the [simplicity_read_buffer8] contract:
    the statements and proofs of [jet_read_buffer8_call.v] and
    [jet_read_buffer8_layout.v] with the chunk list 256, 128, ..., 1.
    The chunk loop itself is the generic [exec_buffer8_read_loop_layout]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_umul128_layout C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout.
Require Import C.jet_write_buffer8_empty_run C.jet_write_buffer8_empty_exec C.jet_read_buffer8_exec.
Require Import C.jet_read_buffer8_call C.jet_read_buffer8_loop_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition buffer511_empty_counts : list Z := [256; 128; 64; 32; 16; 8; 4; 2; 1].
Lemma buffer511_empty_counts_chain : buffer8_empty_chain buffer511_empty_counts.
Proof. vm_compute; repeat split; congruence. Qed.
Lemma buffer511_chunks_chain (x : Ty.tySem (buffer_type (Word 3) 8)) :
  buffer8_empty_chain (map (fun c => Z.of_nat (fst c)) (buffer_byte_chunks 8 x)).
Proof.
  rewrite <- map_map, buffer_byte_chunks_counts.
  change (buffer8_empty_chain buffer511_empty_counts). apply buffer511_empty_counts_chain.
Qed.
Lemma buffer511_chunks_width (x : Ty.tySem (buffer_type (Word 3) 8)) :
  byte_chunks_width (buffer_byte_chunks 8 x) = 4097.
Proof.
  rewrite byte_chunks_width_counts, <- map_map, buffer_byte_chunks_counts. reflexivity.
Qed.
Lemma buffer511_chunks_capacity (x : Ty.tySem (buffer_type (Word 3) 8)) :
  byte_chunks_capacity (buffer_byte_chunks 8 x) = 511%nat.
Proof. rewrite byte_chunks_capacity_counts, buffer_byte_chunks_counts. reflexivity. Qed.

Definition buffer8_read_temps_511 bf base bo output bl slot := PTree.set _n (Vint (Int.repr 8))
  (PTree.set _src (Vptr bf (Ptrofs.repr base)) (PTree.set _len (Vptr bl (Ptrofs.repr slot))
    (PTree.set _buf (Vptr bo (Ptrofs.repr output)) (create_undef_temps f_simplicity_read_buffer8.(fn_temps))))).

Theorem eval_read_buffer8_from_loop_511 m mz mf lef bf base bo output bl slot :
  0 <= slot <= Ptrofs.max_unsigned ->
  Mem.store Mint64 m bl slot (Vlong Int64.zero) = Some mz ->
  Clight2.exec_stmt ge0 empty_env
    (PTree.set _i (Vlong (Int64.repr 256)) (buffer8_read_temps_511 bf base bo output bl slot))
    mz buffer8_read_loop E0 lef mf Out_normal ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
    [Vptr bo (Ptrofs.repr output); Vptr bl (Ptrofs.repr slot); Vptr bf (Ptrofs.repr base); Vint (Int.repr 8)]
    E0 mf Vundef.
Proof.
  intros Hslot HS Hloop. set (le0 := buffer8_read_temps_511 bf base bo output bl slot).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + change (list_norepet [_buf; _len; _src; _n]). vm_compute.
      repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
    + change (list_disjoint [_buf; _len; _src; _n] [_i; _t'2; _t'1; _t'3]); vm_compute; intuition congruence.
    + constructor.
    + reflexivity.
  - rewrite buffer8_read_body_prefix.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
    + apply exec_buffer8_disabled_assert.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mz).
      * eapply exec_Sassign_value with (v := Vlong Int64.zero) (v2 := Vint Int.zero)
          (b := bl) (ofs := Ptrofs.repr slot).
        -- eapply eval_Ederef. apply eval_Etempvar. unfold le0, buffer8_read_temps_511; umul128_lookup.
        -- apply eval_Econst_int.
        -- reflexivity.
        -- apply assign_loc_value with (chunk := Mint64); [reflexivity|].
           unfold Mem.storev. rewrite Ptrofs.unsigned_repr by exact Hslot. exact HS.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
          (le1 := PTree.set _i (Vlong (Int64.repr 256)) le0) (m1 := mz).
        -- apply exec_set. unfold le0, buffer8_read_temps_511; umul128_scalar.
        -- exact Hloop.
  - reflexivity.
  - reflexivity.
Qed.

Theorem eval_read_buffer8_511_layout m bf base bi edge cursor bo output bl slot
    (x : Ty.tySem (buffer_type (Word 3) 8)) :
  0 <= output -> output + 511 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bo output (output + 511) Cur Writable ->
  0 <= slot <= Ptrofs.max_unsigned -> Mem.valid_access m Mint64 bl slot Writable ->
  bf <> bo -> bf <> bi -> bo <> bi -> bl <> bf -> bl <> bo -> bl <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 4097 <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (encode x) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
      [Vptr bo (Ptrofs.repr output); Vptr bl (Ptrofs.repr slot); Vptr bf (Ptrofs.repr base); Vint (Int.repr 8)]
      E0 mf Vundef /\
    uint8_array_at mf bo output (map word8_array_value (byte_chunks_values (buffer_byte_chunks 8 x))) /\
    Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 8 x)))))) /\
    frame_fields_at mf bf base bi edge (cursor + 4097) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 511 <= ofs) ->
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
  assert (HPz : Mem.range_perm mz bo output (output + 511) Cur Writable).
  { intros ofs HR. eapply Mem.perm_store_1; [exact HStore|apply HP; exact HR]. }
  assert (HCellsz : frame_input_cells_at mz bi edge cursor (concat (map byte_chunk_cells (buffer_byte_chunks 8 x)))).
  { rewrite <- buffer_byte_chunks_cells. eapply buffer_input_cells_preserved; [|exact HCells].
    intros ofs w HL. erewrite Mem.load_store_other; [exact HL|exact HStore|left; congruence]. }
  set (le := PTree.set _i (Vlong (Int64.repr 256)) (buffer8_read_temps_511 bf base bo output bl slot)).
  assert (HI : le!_i = Some (Vlong (Int64.repr
    (buffer8_empty_index (map (fun c => Z.of_nat (fst c)) (buffer_byte_chunks 8 x)))))).
  { rewrite <- map_map, buffer_byte_chunks_counts. unfold le. apply PTree.gss. }
  destruct (exec_buffer8_read_loop_layout (buffer_byte_chunks 8 x) mz le bf base bi edge cursor bo output bl slot 0
    (buffer_byte_chunks_sized 8 x) (buffer511_chunks_chain x)
    ltac:(unfold le, buffer8_read_temps_511; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold le, buffer8_read_temps_511; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold le, buffer8_read_temps_511; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    HI HO ltac:(rewrite buffer511_chunks_capacity; exact HM) Hslot ltac:(lia)
    ltac:(rewrite buffer511_chunks_capacity; change (0 + 511 <= 18446744073709551615); lia)
    ltac:(rewrite buffer511_chunks_capacity; exact HPz) HWLenz
    (Mem.load_store_same _ _ _ _ _ _ HStore) Hfo Hfi Hoi Hlf Hlo Hli Hbase HC
    ltac:(rewrite buffer511_chunks_width; exact HMax) HFz HWz HCellsz)
    as (mf & lef & HLoop & HArray & HLen & HFields & HMemory & HPerm & HValid).
  rewrite buffer511_chunks_width in HFields. rewrite buffer511_chunks_capacity in HMemory.
  exists mf. split; [eapply eval_read_buffer8_from_loop_511; eauto|]. split; [exact HArray|].
  split; [rewrite Z.add_0_l in HLen; exact HLen|]. split; [exact HFields|]. split.
  - intros chunk b ofs Hbf Hbo Hbl. rewrite HMemory by assumption.
    eapply Mem.load_store_other; [exact HStore|].
    change (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs). exact Hbl.
  - split; [intros; apply HPerm; eapply Mem.perm_store_1; eauto|
      intros; apply HValid; eapply Mem.store_valid_block_1; eauto].
Qed.

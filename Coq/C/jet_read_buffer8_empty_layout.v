(** Initial-only execution of the actual empty Buffer63 reader. The absent
    payload bits remain arbitrary; all six readBit/forwardBits calls are derived.
    This helper is infrastructure, not a completed individual jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_readBit_layout C.jet_forwardBits_layout C.jet_read_buffer8_exec C.jet_read_buffer8_call.
Require Import C.jet_buffer_input C.jet_buffer_empty_spec C.jet_write_buffer8_empty_run C.jet_write_buffer8_empty_cells.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_buffer8_read_empty_layout m le bf base bi edge cursor xs :
  buffer8_empty_chain xs -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_i = Some (Vlong (Int64.repr (buffer8_empty_index xs))) ->
  frame_base_valid base -> 0 <= cursor -> cursor + buffer8_empty_bits xs <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  frame_input_cells_at m bi edge cursor (buffer8_empty_output_cells xs) ->
  exists mf lef,
    Clight2.exec_stmt ge0 empty_env le m buffer8_read_loop E0 lef mf Out_normal /\
    frame_fields_at mf bf base bi edge (cursor + buffer8_empty_bits xs) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  revert m le cursor. induction xs as [|j xs IH]; intros m le cursor Hchain HS HI HB HC HM HF HW HD HCells.
  - exists m, le. split; [apply exec_buffer8_read_stop; exact HI|].
    split; [rewrite Z.add_0_r; exact HF|]. split; [intros; reflexivity|]. split; auto.
  - destruct Hchain as [HJ [Hhalf Hchain]].
    pose proof (buffer8_empty_bits_nonnegative xs Hchain) as HTBits.
    change (frame_input_cells_at m bi edge cursor
      ((Some false :: repeat None (Z.to_nat (8 * j))) ++ buffer8_empty_output_cells xs)) in HCells.
    apply frame_input_cells_at_app in HCells. destruct HCells as [HHead HTail].
    assert (HFirst : frame_input_bit_at m bi edge cursor false).
    { pose proof (HHead 0%nat (Some false) eq_refl) as H.
      change (frame_input_bit_at m bi edge (cursor + Z.of_nat 0) false) in H.
      replace (cursor + Z.of_nat 0) with cursor in H by lia. exact H. }
    destruct (eval_readBit_layout m bf base bi edge cursor false HB
      ltac:(cbn [buffer8_empty_bits] in HM; lia) HF HFirst HW)
      as (mr & HRead & HFr & HMemr & HPermr & HValidr).
    assert (HWr : Mem.valid_access mr Mint64 bf (base + 8) Writable).
    { destruct HW as [HP HA]. split; [|exact HA]. intros ofs HR; apply HPermr, HP; exact HR. }
    destruct (eval_forwardBits_layout mr bf base bi edge (cursor + 1) (8 * j) HB
      ltac:(lia) ltac:(lia) ltac:(cbn [buffer8_empty_bits] in HM; lia) HFr HWr)
      as (mi & HForward & HFi & HMemi & HPermi & HValidi).
    set (tagged := PTree.set _t'2 (Vint Int.zero) le).
    assert (HBody : Clight2.exec_stmt ge0 empty_env le m buffer8_read_body E0 tagged mi Out_normal).
    { eapply exec_buffer8_read_body with (mr := mr) (bit := false); [reflexivity|exact HS|exact HI|exact HJ|exact HRead|].
      apply exec_buffer8_read_absent with (bf := bf) (base := base) (j := j); [reflexivity| | |lia|exact HForward].
      - unfold tagged; rewrite PTree.gso by discriminate; exact HS.
      - unfold tagged; rewrite PTree.gso by discriminate; exact HI. }
    set (next := PTree.set _i (Vlong (Int64.repr (j / 2))) tagged).
    assert (HUpdate : Clight2.exec_stmt ge0 empty_env tagged mi buffer8_read_update E0 next mi Out_normal).
    { apply exec_buffer8_read_halve; [unfold tagged; rewrite PTree.gso by discriminate; exact HI|lia]. }
    assert (HWNext : Mem.valid_access mi Mint64 bf (base + 8) Writable).
    { destruct HWr as [HP HA]. split; [|exact HA]. intros ofs HR; apply HPermi, HP; exact HR. }
    assert (HWidth : Z.of_nat (@length BitMachine.Cell (Some false :: repeat None (Z.to_nat (8 * j)))) = 1 + 8 * j).
    { cbn [length]. rewrite repeat_length, Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
    rewrite HWidth in HTail.
    assert (HTailNext : frame_input_cells_at mi bi edge (cursor + 1 + 8 * j) (buffer8_empty_output_cells xs)).
    { eapply buffer_input_cells_preserved.
      - intros ofs w HL. rewrite HMemi by (left; congruence). rewrite HMemr by (left; congruence). exact HL.
      - replace (cursor + 1 + 8 * j) with (cursor + (1 + 8 * j)) by lia. exact HTail. }
    destruct (IH mi next (cursor + 1 + 8 * j) Hchain
      ltac:(unfold next, tagged; repeat rewrite PTree.gso by discriminate; exact HS)
      ltac:(unfold next; rewrite PTree.gss, Hhalf; reflexivity) HB ltac:(lia)
      ltac:(cbn [buffer8_empty_bits] in HM; lia) HFi HWNext HD HTailNext)
      as (mf & lef & HRest & HFields & HMemory & HPerm & HValid).
    exists mf, lef. split.
    + unfold buffer8_read_body, buffer8_read_update in HBody, HUpdate.
      rewrite buffer8_read_loop_shape in HBody, HUpdate, HRest |- *.
      eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
        (le1 := tagged) (m1 := mi) (out1 := Out_normal) (le2 := next) (m2 := mi);
        [exact HBody|constructor|exact HUpdate|exact HRest].
    + split.
      * replace (cursor + buffer8_empty_bits (j :: xs)) with
          (cursor + 1 + 8 * j + buffer8_empty_bits xs) by (cbn [buffer8_empty_bits]; lia). exact HFields.
      * split.
        -- intros chunk b ofs Hsep. rewrite HMemory, HMemi, HMemr by exact Hsep. reflexivity.
        -- split; [intros; apply HPerm, HPermi, HPermr; assumption|intros; apply HValid, HValidi, HValidr; assumption].
Qed.

Theorem eval_read_buffer8_empty_layout m bf base bi edge cursor bo output bl slot :
  frame_base_valid base -> 0 <= cursor -> cursor + 510 <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  0 <= slot <= Ptrofs.max_unsigned -> Mem.valid_access m Mint64 bl slot Writable ->
  bf <> bi -> bl <> bf -> bl <> bi ->
  frame_input_cells_at m bi edge cursor (buffer_empty_cells (Word 3) 5) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
      [Vptr bo (Ptrofs.repr output); Vptr bl (Ptrofs.repr slot); Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)]
      E0 mf Vundef /\
    Mem.load Mint64 mf bl slot = Some (Vlong Int64.zero) /\
    frame_fields_at mf bf base bi edge (cursor + 510) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HM HF HW Hslot HWLen Hfi Hlf Hli HCells.
  destruct (Mem.valid_access_store m Mint64 bl slot (Vlong Int64.zero) HWLen) as [mz HStore].
  assert (HFz : frame_fields_at mz bf base bi edge cursor).
  { destruct HF as [HE HO]. split;
      erewrite Mem.load_store_other; [exact HE|exact HStore|left; congruence|
        exact HO|exact HStore|left; congruence]. }
  assert (HWz : Mem.valid_access mz Mint64 bf (base + 8) Writable) by (eapply Mem.store_valid_access_1; eauto).
  assert (HCellsz : frame_input_cells_at mz bi edge cursor (buffer8_empty_output_cells buffer63_empty_counts)).
  { rewrite buffer63_empty_output_canonical. eapply buffer_input_cells_preserved; [|exact HCells].
    intros ofs w HL. erewrite Mem.load_store_other; [exact HL|exact HStore|left; congruence]. }
  set (le := PTree.set _i (Vlong (Int64.repr 32)) (buffer8_read_temps bf base bo output bl slot)).
  destruct (exec_buffer8_read_empty_layout mz le bf base bi edge cursor buffer63_empty_counts
    buffer63_empty_counts_chain ltac:(unfold le, buffer8_read_temps; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold le; apply PTree.gss) HB HC HM HFz HWz Hfi HCellsz)
    as (mf & lef & HLoop & HFields & HMemory & HPerm & HValid).
  exists mf. split; [eapply eval_read_buffer8_from_loop; eauto|]. split.
  - rewrite HMemory by (left; exact Hlf). exact (Mem.load_store_same _ _ _ _ _ _ HStore).
  - split; [exact HFields|]. split.
    + intros chunk b ofs Hbf Hbl. rewrite HMemory by exact Hbf.
      eapply Mem.load_store_other; [exact HStore|].
      change (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs). exact Hbl.
    + split; [intros; apply HPerm; eapply Mem.perm_store_1; eauto|
        intros; apply HValid; eapply Mem.store_valid_block_1; eauto].
Qed.

(** Total initial-memory consumer of one actual canonical buffer-reader step,
    for either absent or present data. Every helper call/store is derived.
    A mixed-chunk loop and public consumers remain separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_input_layout C.jet_frame_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout C.jet_readBit_layout.
Require Import C.jet_read_buffer8_exec C.jet_read_buffer8_tag_layout C.jet_read_buffer8_present_layout.
Require Import C.jet_forwardBits_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_read_chunk_temps le bo output count c :=
  let tagged := PTree.set _t'2 (Vint (bit_int (byte_chunk_tag c))) le in
  match snd c with
  | None => tagged
  | Some xs => buffer8_read_present_temps tagged bo (output + Z.of_nat (length xs)) count
  end.
Lemma buffer8_read_chunk_src le bo output count c :
  (buffer8_read_chunk_temps le bo output count c)!_src = le!_src.
Proof.
  destruct c as [n [xs|]]; unfold buffer8_read_chunk_temps, buffer8_read_present_temps;
    cbn [snd]; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.
Lemma buffer8_read_chunk_len le bo output count c :
  (buffer8_read_chunk_temps le bo output count c)!_len = le!_len.
Proof.
  destruct c as [n [xs|]]; unfold buffer8_read_chunk_temps, buffer8_read_present_temps;
    cbn [snd]; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.
Lemma buffer8_read_chunk_buf le bo output count c :
  le!_buf = Some (Vptr bo (Ptrofs.repr output)) ->
  (buffer8_read_chunk_temps le bo output count c)!_buf =
    Some (Vptr bo (Ptrofs.repr (output + Z.of_nat (length (byte_chunk_values c))))).
Proof.
  intros HB. destruct c as [n [xs|]]; unfold buffer8_read_chunk_temps, buffer8_read_present_temps;
    cbn [snd byte_chunk_values length].
  - rewrite PTree.gso by discriminate. apply PTree.gss.
  - rewrite PTree.gso by discriminate. rewrite Z.add_0_r. exact HB.
Qed.
Lemma exec_buffer8_body_then_halve le next m mf j :
  0 <= j <= Int64.max_unsigned -> next!_i = Some (Vlong (Int64.repr j)) ->
  Clight2.exec_stmt ge0 empty_env le m buffer8_read_body E0 next mf Out_normal ->
  Clight2.exec_stmt ge0 empty_env le m (Ssequence buffer8_read_body buffer8_read_update)
    E0 (PTree.set _i (Vlong (Int64.repr (j / 2))) next) mf Out_normal.
Proof.
  intros HJ HI HB. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := next) (m1 := mf);
    [exact HB|apply exec_buffer8_read_halve; assumption].
Qed.

Theorem exec_buffer8_read_chunk_layout m le bf base bi edge cursor bo output bl slot count c :
  le!_src = Some (Vptr bf (Ptrofs.repr base)) -> le!_buf = Some (Vptr bo (Ptrofs.repr output)) ->
  le!_len = Some (Vptr bl (Ptrofs.repr slot)) -> le!_i = Some (Vlong (Int64.repr (Z.of_nat (fst c)))) ->
  0 < Z.of_nat (fst c) -> (match snd c with None => True | Some xs => length xs = fst c end) ->
  0 <= output -> output + Z.of_nat (fst c) <= Ptrofs.max_unsigned ->
  0 <= slot <= Ptrofs.max_unsigned -> 0 <= count -> count + Z.of_nat (fst c) <= Int64.max_unsigned ->
  Mem.range_perm m bo output (output + Z.of_nat (fst c)) Cur Writable ->
  Mem.valid_access m Mint64 bl slot Writable -> Mem.load Mint64 m bl slot = Some (Vlong (Int64.repr count)) ->
  bf <> bo -> bf <> bi -> bo <> bi -> bl <> bf -> bl <> bo ->
  frame_base_valid base -> 0 <= cursor -> cursor + 1 + 8 * Z.of_nat (fst c) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (byte_chunk_cells c) ->
  exists mf,
    Clight2.exec_stmt ge0 empty_env le m (Ssequence buffer8_read_body buffer8_read_update)
      E0 (PTree.set _i (Vlong (Int64.repr (Z.of_nat (fst c) / 2)))
        (buffer8_read_chunk_temps le bo output count c)) mf Out_normal /\
    uint8_array_at mf bo output (map word8_array_value (byte_chunk_values c)) /\
    Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr (count + Z.of_nat (length (byte_chunk_values c))))) /\
    frame_fields_at mf bf base bi edge (cursor + 1 + 8 * Z.of_nat (fst c)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + Z.of_nat (fst c) <= ofs) ->
      (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HL HI HN HSize HO HM Hslot HC HCount HP HWLen HLoad Hfo Hfi Hoi Hlf Hlo
    Hbase HCursor HMax HF HW HCells.
  assert (HJ : 0 <= Z.of_nat (fst c) <= Int64.max_unsigned) by lia.
  destruct (eval_buffer8_read_tag_layout m bf base bi edge cursor c Hbase ltac:(lia) HF HW Hfi HCells)
    as (mr & HRead & HFrame & HPayload & HMemr & HPermr & HValidr).
  set (tagged := PTree.set _t'2 (Vint (bit_int (byte_chunk_tag c))) le).
  assert (HWFr : Mem.valid_access mr Mint64 bf (base + 8) Writable).
  { destruct HW as [HPerm HA]. split; [|exact HA]. intros ofs HR; apply HPermr, HPerm; exact HR. }
  assert (HLoadr : Mem.load Mint64 mr bl slot = Some (Vlong (Int64.repr count))).
  { rewrite HMemr by (left; exact Hlf). exact HLoad. }
  destruct c as [n [xs|]]; cbn [fst snd] in HSize, HN, HM, HP, HCount, HI, HJ, HMax.
  - assert (HWrLen : Mem.valid_access mr Mint64 bl slot Writable).
    { destruct HWLen as [HPerm HA]. split; [|exact HA]. intros ofs HR; apply HPermr, HPerm; exact HR. }
    assert (HPr : Mem.range_perm mr bo output (output + Z.of_nat (length xs)) Cur Writable).
    { rewrite HSize. intros ofs HR; apply HPermr, HP; exact HR. }
    assert (HSr : tagged!_src = Some (Vptr bf (Ptrofs.repr base))).
    { unfold tagged; rewrite PTree.gso by discriminate; exact HS. }
    assert (HBr : tagged!_buf = Some (Vptr bo (Ptrofs.repr output))).
    { unfold tagged; rewrite PTree.gso by discriminate; exact HB. }
    assert (HLr : tagged!_len = Some (Vptr bl (Ptrofs.repr slot))).
    { unfold tagged; rewrite PTree.gso by discriminate; exact HL. }
    assert (HIr : tagged!_i = Some (Vlong (Int64.repr (Z.of_nat (length xs))))).
    { rewrite HSize. unfold tagged; rewrite PTree.gso by discriminate; exact HI. }
    change (frame_input_cells_at mr bi edge (cursor + 1) (concat (map (@encode (Word 3)) xs))) in HPayload.
    destruct (exec_buffer8_read_present_layout empty_env tagged mr bf base bi edge (cursor + 1)
      bo output bl slot count xs ltac:(reflexivity) HSr HBr HLr HIr HO ltac:(rewrite HSize; exact HM)
      Hslot ltac:(lia) HPr HWrLen HLoadr Hfo Hfi Hoi Hlf Hlo Hbase ltac:(lia)
      ltac:(rewrite HSize; exact HMax) HFrame HWFr HPayload)
      as (mf & HBranch & HArray & HLen & HFields & HMemory & HPerm & HValid).
    assert (HBody : Clight2.exec_stmt ge0 empty_env le m buffer8_read_body E0
      (buffer8_read_chunk_temps le bo output count (n, Some xs)) mf Out_normal).
    { eapply exec_buffer8_read_body with (mr := mr) (bf := bf) (base := base) (j := Z.of_nat n) (bit := true);
        [reflexivity|exact HS|exact HI|lia|exact HRead|exact HBranch]. }
    exists mf. split.
    + apply exec_buffer8_body_then_halve; [exact HJ| |exact HBody].
      unfold buffer8_read_chunk_temps, buffer8_read_present_temps, byte_chunk_tag; cbn [snd].
      repeat rewrite PTree.gso by discriminate; exact HI.
    + split; [exact HArray|]. split; [exact HLen|]. split.
      * rewrite HSize in HFields. exact HFields.
      * split.
        -- intros chunk b ofs Hbf Hbo Hbl. rewrite HMemory; [apply HMemr; exact Hbf|exact Hbf| |exact Hbl].
           rewrite HSize; exact Hbo.
        -- split; [intros; apply HPerm, HPermr; assumption|intros; apply HValid, HValidr; assumption].
  - destruct (eval_forwardBits_layout mr bf base bi edge (cursor + 1) (8 * Z.of_nat n) Hbase
      ltac:(lia) ltac:(lia) HMax HFrame HWFr) as (mf & HForward & HFields & HMemory & HPerm & HValid).
    assert (HBranch : Clight2.exec_stmt ge0 empty_env tagged mr buffer8_read_absent E0 tagged mf Out_normal).
    { apply exec_buffer8_read_absent with (bf := bf) (base := base) (j := Z.of_nat n); [reflexivity| | |exact HJ|exact HForward].
      - unfold tagged; rewrite PTree.gso by discriminate; exact HS.
      - unfold tagged; rewrite PTree.gso by discriminate; exact HI. }
    assert (HBody : Clight2.exec_stmt ge0 empty_env le m buffer8_read_body E0
      (buffer8_read_chunk_temps le bo output count (n, None)) mf Out_normal).
    { eapply exec_buffer8_read_body with (mr := mr) (bf := bf) (base := base) (j := Z.of_nat n) (bit := false);
        [reflexivity|exact HS|exact HI|lia|exact HRead|exact HBranch]. }
    exists mf. split.
    + apply exec_buffer8_body_then_halve; [exact HJ| |exact HBody].
      unfold buffer8_read_chunk_temps; cbn [snd]. rewrite PTree.gso by discriminate; exact HI.
    + split.
      * intros i x Hx. destruct i; discriminate.
      * split.
        -- change (Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr (count + 0)))).
           rewrite Z.add_0_r, HMemory by (left; exact Hlf). exact HLoadr.
        -- split; [exact HFields|]. split.
           ++ intros chunk b ofs Hbf Hbo Hbl. rewrite HMemory, HMemr by exact Hbf. reflexivity.
           ++ split; [intros; apply HPerm, HPermr; assumption|intros; apply HValid, HValidr; assumption].
Qed.

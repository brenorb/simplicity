(** Total actual buffer-writer chunk step from initial byte-array/frame facts.
    The canonical consumer must derive the length/tag invariant; no helper
    execution is a precondition of this result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_buffer_input C.jet_buffer_chunks C.jet_read8s_layout C.jet_readBit_layout.
Require Import C.jet_read_buffer8_tag_layout C.jet_write_buffer8_empty_exec C.jet_write_buffer8_exec.
Require Import C.jet_empty_buffer_segment C.jet_present_buffer_segment.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_write_chunk_temps le bi input len c :=
  let tagged := PTree.set _t'2 (Vint (bit_int (byte_chunk_tag c))) le in
  match snd c with
  | None => tagged
  | Some xs => buffer8_write_present_temps tagged bi input len (Z.of_nat (fst c))
  end.

Lemma buffer8_write_chunk_dst le bi input len c :
  (buffer8_write_chunk_temps le bi input len c)!_dst = le!_dst.
Proof.
  destruct c as [n [xs|]]; unfold buffer8_write_chunk_temps, buffer8_write_present_temps;
    cbn [snd]; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.
Lemma buffer8_write_chunk_buf le bi input len c :
  (match snd c with None => True | Some xs => length xs = fst c end) ->
  le!_buf = Some (Vptr bi (Ptrofs.repr input)) ->
  (buffer8_write_chunk_temps le bi input len c)!_buf =
    Some (Vptr bi (Ptrofs.repr (input + Z.of_nat (length (byte_chunk_values c))))).
Proof.
  intros HSize HB. destruct c as [n [xs|]]; unfold buffer8_write_chunk_temps, buffer8_write_present_temps;
    cbn [snd fst byte_chunk_values length] in *.
  - rewrite PTree.gso by discriminate. rewrite HSize; apply PTree.gss.
  - rewrite PTree.gso by discriminate. rewrite Z.add_0_r; exact HB.
Qed.
Lemma buffer8_write_chunk_len le bi input len c :
  (match snd c with None => True | Some xs => length xs = fst c end) ->
  le!_len = Some (Vlong (Int64.repr len)) ->
  (buffer8_write_chunk_temps le bi input len c)!_len =
    Some (Vlong (Int64.repr (len - Z.of_nat (length (byte_chunk_values c))))).
Proof.
  intros HSize HL. destruct c as [n [xs|]]; unfold buffer8_write_chunk_temps, buffer8_write_present_temps;
    cbn [snd fst byte_chunk_values length] in *.
  - rewrite HSize; apply PTree.gss.
  - rewrite PTree.gso by discriminate. rewrite Z.sub_0_r; exact HL.
Qed.

Lemma exec_buffer8_write_body_then_halve le next m mf j :
  0 <= j <= Int64.max_unsigned -> next!_i = Some (Vlong (Int64.repr j)) ->
  Clight2.exec_stmt ge0 empty_env le m buffer8_loop_body E0 next mf Out_normal ->
  Clight2.exec_stmt ge0 empty_env le m (Ssequence buffer8_loop_body buffer8_loop_update)
    E0 (PTree.set _i (Vlong (Int64.repr (j / 2))) next) mf Out_normal.
Proof.
  intros HJ HI HB. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := next) (m1 := mf);
    [exact HB|apply exec_buffer8_write_halve; assumption].
Qed.

Theorem exec_buffer8_write_chunk_layout m le bi input bf base bw edge cursor len c tail :
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) -> le!_buf = Some (Vptr bi (Ptrofs.repr input)) ->
  le!_len = Some (Vlong (Int64.repr len)) -> le!_i = Some (Vlong (Int64.repr (Z.of_nat (fst c)))) ->
  0 < Z.of_nat (fst c) -> (match snd c with None => True | Some xs => length xs = fst c end) ->
  0 <= len <= Int64.max_unsigned -> byte_chunk_tag c = (Z.of_nat (fst c) <=? len) ->
  0 <= tail -> 0 <= input -> input + Z.of_nat (fst c) <= Ptrofs.max_unsigned ->
  bi <> bf -> bi <> bw -> uint8_array_at m bi input (map word8_array_value (byte_chunk_values c)) ->
  write_frame_at m bf base bw edge cursor (1 + 8 * Z.of_nat (fst c) + tail) ->
  exists mf,
    Clight2.exec_stmt ge0 empty_env le m (Ssequence buffer8_loop_body buffer8_loop_update)
      E0 (PTree.set _i (Vlong (Int64.repr (Z.of_nat (fst c) / 2)))
        (buffer8_write_chunk_temps le bi input len c)) mf Out_normal /\
    frame_output_cells_at mf bw edge cursor (byte_chunk_cells c) /\
    write_prefix_at m mf bw edge cursor /\
    write_frame_at mf bf base bw edge (cursor - (1 + 8 * Z.of_nat (fst c))) tail /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - (1 + 8 * Z.of_nat (fst c))) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HD HB HL HI HN HSize HLen HChoice HT HInput HMax Hif Hiw HA HW.
  pose proof HW as [_ [_ [_ [HFrameCount [HC _]]]]].
  assert (HJ : 0 <= Z.of_nat (fst c) <= Int64.max_unsigned) by lia.
  destruct c as [n [xs|]]; cbn [fst snd byte_chunk_tag] in HSize, HN, HI, HChoice, HMax, HJ, HW.
  - assert (HDec : (Z.of_nat n <=? len) = Datatypes.true) by (symmetry; exact HChoice).
    assert (HNLen : Z.of_nat n <= len) by (apply Z.leb_le; exact HDec).
    destruct (eval_present_buffer_segment m bi input bf base bw edge cursor xs tail
      ltac:(lia) HT HInput ltac:(rewrite HSize; exact HMax) Hif Hiw HA ltac:(rewrite HSize; exact HW))
      as (mb & mf & HBit & HBytes & HCells & HPrefix & HFrame & HMem & HPerm & HValid).
    set (tagged := PTree.set _t'2 (Vint Int.one) le).
    assert (HBranch : Clight2.exec_stmt ge0 empty_env tagged mb buffer8_present_branch E0
      (buffer8_write_present_temps tagged bi input len (Z.of_nat n)) mf Out_normal).
    { eapply exec_buffer8_write_present with (bf := bf) (base := base);
        [reflexivity| | | | |exact HInput|exact HMax|lia|rewrite <- HSize; exact HBytes];
        unfold tagged; rewrite PTree.gso by discriminate; assumption. }
    assert (HBody : Clight2.exec_stmt ge0 empty_env le m buffer8_loop_body E0
      (buffer8_write_chunk_temps le bi input len (n, Some xs)) mf Out_normal).
    { eapply exec_buffer8_write_body with (mb := mb) (bf := bf) (base := base) (j := Z.of_nat n) (len := len);
        [reflexivity|exact HD|exact HI|exact HL|lia|exact HLen| | ].
      - rewrite HDec; exact HBit.
      - rewrite HDec; exact HBranch. }
    exists mf. split.
    + apply exec_buffer8_write_body_then_halve; [exact HJ| |exact HBody].
      unfold buffer8_write_chunk_temps, buffer8_write_present_temps; cbn [snd].
      repeat rewrite PTree.gso by discriminate; exact HI.
    + split; [exact HCells|]. split; [exact HPrefix|].
      rewrite HSize in HFrame, HMem. exact (conj HFrame (conj HMem (conj HPerm HValid))).
  - assert (HDec : (Z.of_nat n <=? len) = Datatypes.false) by (symmetry; exact HChoice).
    assert (HCount : Z.of_nat (Z.to_nat (8 * Z.of_nat n)) = 8 * Z.of_nat n) by (apply Z2Nat.id; lia).
    destruct (eval_empty_buffer_segment m bf base bw edge cursor (Z.to_nat (8 * Z.of_nat n)) tail
      HT ltac:(rewrite HCount; exact HW))
      as (mb & mf & HBit & HSkip & HCells & HPrefix & HFrame & HMem & HPerm & HValid).
    rewrite HCount in HSkip, HFrame, HMem.
    set (tagged := PTree.set _t'2 (Vint Int.zero) le).
    assert (HBranch : Clight2.exec_stmt ge0 empty_env tagged mb buffer8_skip_call E0 tagged mf Out_normal).
    { apply exec_buffer8_write_absent with (bf := bf) (base := base) (j := Z.of_nat n);
        [reflexivity| | |exact HJ|exact HSkip];
        unfold tagged; rewrite PTree.gso by discriminate; assumption. }
    assert (HBody : Clight2.exec_stmt ge0 empty_env le m buffer8_loop_body E0
      (buffer8_write_chunk_temps le bi input len (n, None)) mf Out_normal).
    { eapply exec_buffer8_write_body with (mb := mb) (bf := bf) (base := base) (j := Z.of_nat n) (len := len);
        [reflexivity|exact HD|exact HI|exact HL|lia|exact HLen| | ].
      - rewrite HDec; exact HBit.
      - rewrite HDec; exact HBranch. }
    exists mf. split.
    + apply exec_buffer8_write_body_then_halve; [exact HJ| |exact HBody].
      unfold buffer8_write_chunk_temps; cbn [snd]. rewrite PTree.gso by discriminate; exact HI.
    + split.
      * change (frame_output_cells_at mf bw edge cursor (Some Datatypes.false :: repeat None (8 * n))).
        replace (Z.to_nat (8 * Z.of_nat n)) with (8 * n)%nat in HCells by
          (rewrite Z2Nat.inj_mul by lia; rewrite Nat2Z.id; reflexivity). exact HCells.
      * exact (conj HPrefix (conj HFrame (conj HMem (conj HPerm HValid)))).
Qed.

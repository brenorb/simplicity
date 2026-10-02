(** Derive the complete actual present-buffer branch from initial canonical
    byte cells and writable locals. No reader call or length store is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_read_buffer8_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_buffer8_read_present_layout e le m bf base bi edge cursor bo output bl slot
    count (xs : list (Ty.tySem (Word 3))) :
  e!_read8s = None -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_buf = Some (Vptr bo (Ptrofs.repr output)) -> le!_len = Some (Vptr bl (Ptrofs.repr slot)) ->
  le!_i = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) ->
  0 <= output -> output + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  0 <= slot <= Ptrofs.max_unsigned -> 0 <= count <= Int64.max_unsigned ->
  Mem.range_perm m bo output (output + Z.of_nat (length xs)) Cur Writable ->
  Mem.valid_access m Mint64 bl slot Writable ->
  Mem.load Mint64 m bl slot = Some (Vlong (Int64.repr count)) ->
  bf <> bo -> bf <> bi -> bo <> bi -> bl <> bf -> bl <> bo ->
  frame_base_valid base -> 0 <= cursor -> cursor + 8 * Z.of_nat (length xs) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  frame_input_cells_at m bi edge cursor (concat (map (@encode (Word 3)) xs)) ->
  exists mf,
    Clight2.exec_stmt ge0 e le m buffer8_read_present E0
      (buffer8_read_present_temps le bo (output + Z.of_nat (length xs)) count) mf Out_normal /\
    uint8_array_at mf bo output (map word8_array_value xs) /\
    Mem.load Mint64 mf bl slot = Some (Vlong (Int64.repr (count + Z.of_nat (length xs)))) /\
    frame_fields_at mf bf base bi edge (cursor + 8 * Z.of_nat (length xs)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + Z.of_nat (length xs) <= ofs) ->
      (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HE HS HB HL HI HO HM Hslot Hcount HP HWLen Hload Hfo Hfi Hoi Hlf Hlo
    Hbase HC Hmax HF HW HCells.
  pose proof (proj1 (frame_input_byte_list m bi edge cursor xs) HCells) as HInput.
  destruct (eval_read8s_layout m bo output bf base bi edge cursor xs HO HM HP Hfo Hfi Hoi
    Hbase HC Hmax HF HW HInput) as (mr & HRead & HArray & HFrame & HMemory & HPerm & HValid).
  assert (HWLenr : Mem.valid_access mr Mint64 bl slot Writable).
  { destruct HWLen as [HPermLen HAlign]. split; [|exact HAlign]. intros ofs Hrange.
    apply HPerm, HPermLen; exact Hrange. }
  assert (Hloadr : Mem.load Mint64 mr bl slot = Some (Vlong (Int64.repr count))).
  { rewrite HMemory; [exact Hload|left; exact Hlf|left; exact Hlo]. }
  destruct (Mem.valid_access_store mr Mint64 bl slot
    (Vlong (Int64.repr (count + Z.of_nat (length xs)))) HWLenr) as [mf HStore].
  exists mf. split.
  - eapply exec_buffer8_read_present; [exact HE|exact HS|exact HB|exact HL|exact HI|
      exact HO|exact HM|exact Hslot|split; [lia|lia]|exact Hcount|exact HRead|exact Hloadr|exact HStore].
  - split.
    + intros i x Hx. erewrite Mem.load_store_other; [exact (HArray i x Hx)|exact HStore|left; congruence].
    + split; [exact (Mem.load_store_same _ _ _ _ _ _ HStore)|]. split.
      * destruct HFrame as [HEdge HCursor]. split;
          erewrite Mem.load_store_other; [exact HEdge|exact HStore|left; congruence|
            exact HCursor|exact HStore|left; congruence].
      * split.
        -- intros chunk b ofs Hbf Hbo Hbl.
           erewrite Mem.load_store_other; [apply HMemory; assumption|exact HStore|].
           change (b <> bl \/ ofs + size_chunk chunk <= slot \/ slot + 8 <= ofs). exact Hbl.
        -- split.
           ++ intros b ofs kind p H. eapply Mem.perm_store_1; [exact HStore|apply HPerm; exact H].
           ++ intros b H. eapply Mem.store_valid_block_1; [exact HStore|apply HValid; exact H].
Qed.

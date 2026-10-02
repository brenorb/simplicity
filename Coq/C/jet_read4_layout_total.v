(** Total actual nibble reader, including word-boundary crossings.
    Its Word4 representation bridge remains a separate obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_read4_layout C.jet_read4_crossing_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition read4_layout_result cursor high low :=
  if Z_le_dec (cursor mod 64) 60
  then read4_at (cursor mod 64) high
  else read4_crossing_result (64 - cursor mod 64) high low.

Theorem eval_read4_layout m bf base bw edge cursor high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 4 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (60 < cursor mod 64 ->
    8 * (2 + cursor / 64) <= edge /\
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read4)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (read4_layout_result cursor high low)) /\
    frame_fields_at mf bf base bw edge (cursor + 4) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HE HF HH HLow PW HD.
  destruct HF as [HF HO].
  assert (HM : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  unfold read4_layout_result. destruct (Z_le_dec (cursor mod 64) 60) as [HN | HX].
  - destruct (Mem.valid_access_store m Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor + 4))) PW) as [mf SF].
    exists mf. split.
    + eapply eval_read4_layout_non_crossing; eauto. split; assumption.
    + split.
      * split.
        -- erewrite Mem.load_store_other; [exact HF|exact SF|].
           right; left; change (base + 8 <= base + 8); lia.
        -- exact (Mem.load_store_same _ _ _ _ _ _ SF).
      * split.
        -- intros chunk b ofs Hdisjoint. eapply Mem.load_store_other; [exact SF|].
           change (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs).
           tauto || lia.
        -- split.
           ++ intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
           ++ intros b HV. eapply Mem.store_valid_block_1; eauto.
  - destruct (HLow ltac:(lia)) as [HE2 HL].
    destruct (Mem.valid_access_store m Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor + (64 - cursor mod 64)))) PW) as [mm SM].
    assert (PWm : Mem.valid_access mm Mint64 bf (base + 8) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mm Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor + 4))) PWm) as [mf SF].
    exists mf. split.
    + eapply eval_read4_layout_crossing_raw; eauto; try lia.
      * split; assumption.
      * erewrite Mem.load_store_other; [exact HL|exact SM|auto].
      * exact (Mem.load_store_same _ _ _ _ _ _ SM).
    + split.
      * split.
        -- erewrite Mem.load_store_other; [|exact SF|right; left; change (base + 8 <= base + 8); lia].
           erewrite Mem.load_store_other; [exact HF|exact SM|right; left; change (base + 8 <= base + 8); lia].
        -- exact (Mem.load_store_same _ _ _ _ _ _ SF).
      * split.
        -- intros chunk b ofs Hdisjoint.
           assert (HSep : b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs) by lia.
           erewrite Mem.load_store_other; [|exact SF|exact HSep].
           eapply Mem.load_store_other; eauto.
        -- split.
           ++ intros b ofs kind p HP. eauto using Mem.perm_store_1.
           ++ intros b HV. eauto using Mem.store_valid_block_1.
Qed.


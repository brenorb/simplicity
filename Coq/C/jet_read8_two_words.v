(** A complete two-word byte reader, including every crossing and exact boundary.
    Its final contract contains only initial frame loads and write permission. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_read8 C.jet_read8_position C.jet_read8_two_positions.
Require Import C.jet_read8_crossing C.jet_read8_crossing_word C.jet_crossing_word C.jet_frame_spec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition two_word_byte cursor high low :=
  if Z_le_dec cursor 56 then Int64.shru high (Int64.repr (56 - cursor))
  else if Z_lt_dec cursor 64 then crossing_byte (64 - cursor) high low
  else Int64.shru low (Int64.repr (120 - cursor)).

Theorem eval_read8_two_words m bf bw cursor high low :
  0 <= cursor <= 120 ->
  frame_fields m bf bw 16 cursor ->
  Mem.load Mint64 m bw 8 = Some (Vlong high) ->
  Mem.load Mint64 m bw 0 = Some (Vlong low) ->
  Mem.valid_access m Mint64 bf 8 Writable ->
  bf <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
      [Vptr bf Ptrofs.zero] E0 mf (Vint (read8_result (two_word_byte cursor high low))) /\
    frame_fields mf bf bw 16 (cursor + 8) /\
    (forall chunk b ofs, b <> bf -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC [HE HO] HH HL PW HD.
  unfold two_word_byte.
  destruct (Z_le_dec cursor 56) as [HHalf | HOther].
  - destruct (Mem.valid_access_store m Mint64 bf 8 (Vlong (Int64.repr (cursor + 8))) PW)
      as [mf SF].
    exists mf. split.
    + eapply eval_read8_high; eauto; lia.
    + split.
      * split.
        -- erewrite Mem.load_store_other; [exact HE|exact SF|right; left; change (0 + 8 <= 8); lia].
        -- exact (Mem.load_store_same _ _ _ _ _ _ SF).
      * split.
        -- intros chunk b ofs Hbf. eapply Mem.load_store_other; [exact SF|auto].
        -- split.
           ++ intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
           ++ intros b HV. eapply Mem.store_valid_block_1; eauto.
  - destruct (Z_lt_dec cursor 64) as [HCross | HLow].
    + destruct (Mem.valid_access_store m Mint64 bf 8 (Vlong (Int64.repr 64)) PW)
        as [mm SM].
      assert (PWm : Mem.valid_access mm Mint64 bf 8 Writable)
        by (eapply Mem.store_valid_access_1; eauto).
      destruct (Mem.valid_access_store mm Mint64 bf 8 (Vlong (Int64.repr (cursor + 8))) PWm)
        as [mf SF].
      exists mf. split.
      * rewrite <- read8_crossing_denotes_slice by lia.
        eapply eval_read8_crossing; eauto; try lia.
        -- replace (64 - (64 - cursor)) with cursor by lia. exact HO.
        -- replace (72 - (64 - cursor)) with (cursor + 8) by lia. exact SF.
      * split.
        -- split.
           ++ erewrite Mem.load_store_other; [|exact SF|right; left; change (0 + 8 <= 8); lia].
              erewrite Mem.load_store_other; [exact HE|exact SM|right; left; change (0 + 8 <= 8); lia].
           ++ exact (Mem.load_store_same _ _ _ _ _ _ SF).
        -- split.
           ++ intros chunk b ofs Hbf. erewrite Mem.load_store_other; [|exact SF|auto].
              eapply Mem.load_store_other; [exact SM|auto].
           ++ split.
              ** intros b ofs kind p HP. eauto using Mem.perm_store_1.
              ** intros b HV. eauto using Mem.store_valid_block_1.
    + destruct (Mem.valid_access_store m Mint64 bf 8 (Vlong (Int64.repr (cursor + 8))) PW)
        as [mf SF].
      exists mf. split.
      * replace (120 - cursor) with (56 - (cursor - 64)) by lia.
        eapply eval_read8_low; eauto; lia.
      * split.
        -- split.
           ++ erewrite Mem.load_store_other; [exact HE|exact SF|right; left; change (0 + 8 <= 8); lia].
           ++ exact (Mem.load_store_same _ _ _ _ _ _ SF).
        -- split.
           ++ intros chunk b ofs Hbf. eapply Mem.load_store_other; [exact SF|auto].
           ++ split.
              ** intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
              ** intros b HV. eapply Mem.store_valid_block_1; eauto.
Qed.

(** Initial-only actual helper call crossing both words with the larger
    initial source shift. The actual first loop iteration reaches its second
    return. All four stores and intervening next-word loads are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_word_bits.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Require Import C.jet_copyBits_right_advance C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_copyBits_two_words_right_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_copy_helper_two_right_full m bd base bs sbase bi edge rc bw outedge cursor n old source next :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (2 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> 8 <= write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < cursor mod 64 -> cursor mod 64 < 64 - rc mod 64 -> 64 - rc mod 64 < n <= 64 -> n <= cursor ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  (bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (2 + rc / 64)) ->
  (bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor - 8 \/
    write_word_address outedge cursor - 8 + 8 <= edge - 8 * (2 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 m bw (write_word_address outedge cursor) = Some (Vlong old) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor - 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
      Some (Vlong (copy_loop_join_value (64 - rc mod 64 - cursor mod 64) source next)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor - 8 \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hpartial Hshift Hn Hnc Hbd Hsep Hsepnext Hsepnextlow Hsource Hnext Hold PW PWlow.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (HfirstEdge : 8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned) by lia.
  assert (Hnextaddr : 0 <= edge - 8 * (2 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hnextptr : Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + rc / 64))) (Ptrofs.repr 8) =
      Ptrofs.repr (edge - 8 * (2 + rc / 64))).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by exact Hsrcaddr.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. f_equal; lia. }
  assert (Hdstaddr : 0 <= write_word_address outedge cursor <= Ptrofs.max_unsigned) by lia.
  assert (Hlowaddr : 0 <= write_word_address outedge cursor - 8 <= Ptrofs.max_unsigned) by lia.
  assert (Hlowptr : Ptrofs.sub (Ptrofs.repr (write_word_address outedge cursor)) (Ptrofs.repr 8) =
      Ptrofs.repr (write_word_address outedge cursor - 8)).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by exact Hdstaddr.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. reflexivity. }
  destruct (Mem.valid_access_store m Mint64 bw (write_word_address outedge cursor)
    (Vlong (clear_low (cursor mod 64) old)) PW) as [mc SC].
  assert (HsourceC : Mem.load Mint64 mc bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source)).
  { erewrite Mem.load_store_other; [exact Hsource|exact SC|exact Hsep]. }
  assert (PWC : Mem.valid_access mc Mint64 bw (write_word_address outedge cursor) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mc Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) PWC) as [mp SP].
  assert (HsourceP : Mem.load Mint64 mp bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source)).
  { erewrite Mem.load_store_other; [exact HsourceC|exact SP|exact Hsep]. }
  assert (PWlowP : Mem.valid_access mp Mint64 bw (write_word_address outedge cursor - 8) Writable).
  { eapply Mem.store_valid_access_1; [exact SP|].
    eapply Mem.store_valid_access_1; [exact SC|exact PWlow]. }
  destruct (Mem.valid_access_store mp Mint64 bw (write_word_address outedge cursor - 8)
    (Vlong (copy_loop_value (64 - rc mod 64 - cursor mod 64) source)) PWlowP) as [mi SI].
  assert (HnextI : Mem.load Mint64 mi bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next)).
  { erewrite Mem.load_store_other; [|exact SI|exact Hsepnextlow].
    erewrite Mem.load_store_other; [|exact SP|exact Hsepnext].
    erewrite Mem.load_store_other; [exact Hnext|exact SC|exact Hsepnext]. }
  assert (PWlowI : Mem.valid_access mi Mint64 bw (write_word_address outedge cursor - 8) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mi Mint64 bw (write_word_address outedge cursor - 8)
    (Vlong (copy_loop_join_value (64 - rc mod 64 - cursor mod 64) source next)) PWlowI) as [mf SF].
  exists mf. split.
  - assert (HAmax : write_word_address outedge cursor <= Ptrofs.max_unsigned) by lia.
    eapply eval_copy_helper_prefix_composes; try eassumption; [|right; reflexivity].
    eapply exec_copy_tail_two_right with
      (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
      (dst_ofs := Ptrofs.repr (write_word_address outedge cursor)) (mc := mc) (mp := mp)
      (bi := bi) (bw := bw) (ss := 64 - rc mod 64) (ds := cursor mod 64)
      (n := n) (old := old) (source := source); try lia.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env, copy_frame_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact Hold.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SC.
    + rewrite Ptrofs.unsigned_repr by exact Hsrcaddr; exact HsourceC.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SP.
    + eapply exec_copy_loop_full with (bi := bi) (bw := bw) (mi := mi) (next := next)
        (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
        (dst_ofs := Ptrofs.sub (Ptrofs.repr (write_word_address outedge cursor)) (Ptrofs.repr 8))
        (ss := 64 - rc mod 64 - cursor mod 64) (n := n - cursor mod 64) (source := source); try lia.
      * unfold copy_two_right_env, copy_right_advance_env, copy_right_env, copy_clear_env,
          copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * unfold copy_two_right_env, copy_right_advance_env. rewrite PTree.gss; reflexivity.
      * unfold copy_two_right_env, copy_right_advance_env.
        rewrite PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * unfold copy_two_right_env, copy_right_advance_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * rewrite Ptrofs.unsigned_repr by exact Hsrcaddr; exact HsourceP.
      * rewrite Hlowptr, Ptrofs.unsigned_repr by exact Hlowaddr; exact SI.
      * rewrite Hnextptr, Ptrofs.unsigned_repr by exact Hnextaddr; exact HnextI.
      * rewrite Hlowptr, Ptrofs.unsigned_repr by exact Hlowaddr; exact SF.
  - split.
    + erewrite Mem.load_store_other; [|exact SF|].
      2: { right; right; change (write_word_address outedge cursor - 8 + 8 <= write_word_address outedge cursor); lia. }
      erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ SP)|exact SI|].
      right; right; change (write_word_address outedge cursor - 8 + 8 <= write_word_address outedge cursor); lia.
    + split; [exact (Mem.load_store_same _ _ _ _ _ _ SF)|]. split.
      * destruct HW as [Hedge Hcursor]. split.
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           erewrite Mem.load_store_other; [|exact SI|auto].
           erewrite Mem.load_store_other; [|exact SP|auto].
           erewrite Mem.load_store_other; [exact Hedge|exact SC|auto].
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           erewrite Mem.load_store_other; [|exact SI|auto].
           erewrite Mem.load_store_other; [|exact SP|auto].
           erewrite Mem.load_store_other; [exact Hcursor|exact SC|auto].
      * split.
        -- intros chunk b ofs Houtside.
           assert (HH : b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
               write_word_address outedge cursor + 8 <= ofs) by (intuition lia).
           assert (HL : b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor - 8 \/
               write_word_address outedge cursor - 8 + 8 <= ofs) by (intuition lia).
           erewrite Mem.load_store_other; [|exact SF|exact HL].
           erewrite Mem.load_store_other; [|exact SI|exact HL].
           erewrite Mem.load_store_other; [|exact SP|exact HH].
           eapply Mem.load_store_other; [exact SC|exact HH].
        -- split.
           ++ intros b ofs kind p HP; eauto using Mem.perm_store_1.
           ++ intros b HV; eauto using Mem.store_valid_block_1.
Qed.

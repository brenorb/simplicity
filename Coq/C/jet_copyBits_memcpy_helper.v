(** Initial-only contracts of the actual [copyBitsHelper] on its two plain
    [memcpy] paths for counts up to one word: both frames aligned, and equal
    initial shifts after the partial-word prefix.  Both are conditional on the
    explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_word_bits C.jet_frame_constants.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Require Import C.jet_copyBits_right_advance C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing.
Require Import C.jet_copyBits_two_words_right_exec C.jet_memcpy_model C.jet_copyBits_memcpy_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 30.

(** One 64-bit word copied by the modelled [memcpy]. *)
Lemma memcpy_word_effect (Hmodel : memcpy_model) m bi src bw dst v :
  Mem.load Mint64 m bi src = Some (Vlong v) -> Mem.valid_access m Mint64 bw dst Writable ->
  0 <= src <= Ptrofs.max_unsigned -> 0 <= dst <= Ptrofs.max_unsigned ->
  (bi <> bw \/ src + 8 <= dst \/ dst + 8 <= src) ->
  exists m',
    external_call (EF_external "memcpy" memcpy_sig) ge0
      [Vptr bw (Ptrofs.repr dst); Vptr bi (Ptrofs.repr src); Vlong (Int64.repr 8)]
      m E0 (Vptr bw (Ptrofs.repr dst)) m' /\
    Mem.load Mint64 m' bw dst = Some (Vlong v) /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= dst \/ dst + 8 <= ofs ->
      Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm m' b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HL [HW HAl] Hs Hd Hsep.
  destruct (Mem.load_loadbytes _ _ _ _ _ HL) as [bytes [HBytes Hdec]].
  change (size_chunk Mint64) with 8 in HBytes.
  assert (Hlen : length bytes = 8%nat) by (apply (Mem.loadbytes_length _ _ _ _ _ HBytes)).
  destruct (Hmodel ge0 m bw (Ptrofs.repr dst) bi (Ptrofs.repr src) 8 bytes) as [m' [HS HE]].
  - rewrite !Ptrofs.unsigned_repr by lia. exact HBytes.
  - rewrite Ptrofs.unsigned_repr by lia. intros ofs Hofs. apply HW. change (size_chunk Mint64) with 8. lia.
  - rewrite !Ptrofs.unsigned_repr by lia. lia.
  - change Int64.max_unsigned with 18446744073709551615; lia.
  - rewrite Ptrofs.unsigned_repr in HS by lia.
    exists m'. split; [exact HE|].
    assert (HL' : Mem.loadbytes m' bw dst 8 = Some bytes).
    { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as Hsame.
      rewrite Hlen in Hsame. exact Hsame. }
    split.
    + rewrite (Mem.loadbytes_load Mint64 m' bw dst bytes HL' HAl). rewrite <- Hdec. reflexivity.
    + split.
      * intros chunk b ofs Hout. eapply Mem.load_storebytes_other; [exact HS|].
        rewrite Hlen. change (Z.of_nat 8) with 8. destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
      * split.
        -- intros b ofs kind p HP. eapply Mem.perm_storebytes_1; eauto.
        -- intros b HV. eapply Mem.storebytes_valid_block_1; eauto.
Qed.

Lemma exec_copy_choice_memcpy le m m' bi src_ofs bw dst_ofs ss n :
  (ss = 0 \/ ss = 64) -> 1 <= n <= 64 ->
  le!_dst_ptr = Some (Vptr bw dst_ofs) -> le!_src_ptr = Some (Vptr bi src_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  external_call (EF_external "memcpy" memcpy_sig) ge0
    [Vptr bw dst_ofs; Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (1 - ss / 64)))); Vlong (Int64.repr 8)]
    m E0 (Vptr bw dst_ofs) m' ->
  Clight2.exec_stmt ge0 empty_env le m copy_tail_after_partial E0 (copy_mcpy_env le) m' Out_normal.
Proof.
  intros Hss Hn HD HS HSS HN Hext.
  assert (Hmod : Int64.modu (Int64.repr ss) (Int64.repr 64) = Int64.zero).
  { destruct Hss as [-> | ->]; reflexivity. }
  rewrite copy_tail_choice_shape.
  eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
  - eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong Int64.zero).
    + apply eval_Econst_int.
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr 64));
        [apply eval_Etempvar; exact HSS|apply eval_generated_uword_bits|].
      simpl. unfold sem_mod, sem_binarith. simpl.
      assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity.
      rewrite Hmod. reflexivity.
    + vm_compute. reflexivity.
  - reflexivity.
  - eapply exec_copy_memcpy_branch; eassumption.
Qed.

Theorem eval_copy_helper_memcpy_aligned (Hmodel : memcpy_model) m bd base bs sbase bi edge rc bw outedge cursor n source :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  rc mod 64 = 0 -> cursor mod 64 = 0 -> 0 < n <= 64 -> n <= cursor -> bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) = Some (Vlong source) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hrz Hcz Hn Hnc Hbd Hsep Hsource Hdst.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hdstaddr : 0 <= write_word_address outedge cursor <= Ptrofs.max_unsigned).
  { unfold write_word_address in *. pose proof (Z.div_pos (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
  destruct (memcpy_word_effect Hmodel m bi (edge - 8 * (1 + rc / 64)) bw
    (write_word_address outedge cursor) source Hsource Hdst Hsrcaddr Hdstaddr Hsep)
    as (mf & Hext & Hword & Hother & Hperm & Hvalid).
  exists mf. split.
  - eapply eval_copy_helper_prefix_composes with (out := Out_normal); try eassumption; [|left; reflexivity].
    rewrite copy_helper_tail_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := copy_helper_env bd base bs sbase n bi edge rc bw outedge cursor).
    + eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := Datatypes.false).
      * apply eval_Etempvar. unfold copy_helper_env, copy_dst_shift_env.
        rewrite PTree.gss, Hcz. reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + eapply exec_copy_choice_memcpy with (bi := bi) (bw := bw) (ss := 64)
        (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
        (dst_ofs := Ptrofs.repr (write_word_address outedge cursor)) (n := n); try lia.
      * unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss.
        rewrite Hrz. reflexivity.
      * unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env, copy_frame_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * assert (Hz : 8 * (1 - 64 / 64) = 0) by reflexivity. rewrite Hz.
        change (Ptrofs.repr 0) with Ptrofs.zero. rewrite Ptrofs.sub_zero_l. exact Hext.
  - split; [exact Hword|]. split.
    + destruct HW as [Hedge Hcursor]. split.
      * rewrite Hother; [exact Hedge|left; exact Hbd].
      * rewrite Hother; [exact Hcursor|left; exact Hbd].
    + split; [exact Hother|]. split; [exact Hperm|exact Hvalid].
Qed.

Lemma exec_copy_tail_memcpy_equal le m mc mp m' bi src_ofs bw dst_ofs ds n old source :
  1 <= ds <= 63 -> ds < n <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ds)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ds ds old source)) = Some mp ->
  external_call (EF_external "memcpy" memcpy_sig) ge0
    [Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8));
     Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (1 - 0 / 64)))); Vlong (Int64.repr 8)]
    mp E0 (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8))) m' ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0
    (copy_mcpy_env (copy_two_right_env le bw dst_ofs ds ds n old source)) m' Out_normal.
Proof.
  intros Hds Hn HP HD HS HDS HN Hold SC Hsource SP Hext.
  assert (Hnonzero : Int64.eq (Int64.repr ds) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ds <= 18446744073709551615); lia).
    change (ds = 0) in HE; lia. }
  rewrite copy_helper_tail_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mp)
    (le1 := copy_two_right_env le bw dst_ofs ds ds n old source).
  - eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
    + copy_temp.
    + change (Some (negb (Int64.eq (Int64.repr ds) Int64.zero)) = Some true).
      rewrite Hnonzero; reflexivity.
    + eapply exec_copy_partial_continue_right; try eassumption; lia.
  - eapply exec_copy_choice_memcpy with (bi := bi) (bw := bw) (ss := 0)
      (src_ofs := src_ofs) (dst_ofs := Ptrofs.sub dst_ofs (Ptrofs.repr 8)) (n := n - ds); try lia.
    + unfold copy_two_right_env, copy_right_advance_env. rewrite PTree.gss; reflexivity.
    + unfold copy_two_right_env, copy_right_advance_env.
      rewrite !PTree.gso by discriminate. 
      unfold copy_right_env, copy_clear_env. rewrite !PTree.gso by discriminate. exact HP.
    + unfold copy_two_right_env, copy_right_advance_env.
      rewrite PTree.gso by discriminate. rewrite PTree.gss. rewrite Z.sub_diag. reflexivity.
    + unfold copy_two_right_env, copy_right_advance_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
    + exact Hext.
Qed.

Theorem eval_copy_helper_memcpy_equal (Hmodel : memcpy_model) m bd base bs sbase bi edge rc bw outedge cursor n old source next :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (2 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> 8 <= write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < cursor mod 64 -> cursor mod 64 = 64 - rc mod 64 -> cursor mod 64 < n <= 64 -> n <= cursor ->
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
    Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) = Some (Vlong next) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor - 8 \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hpartial Hshift Hn Hnc Hbd Hsep Hsepnext Hsepnextlow
    Hsource Hnext Hold PW PWlow.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (HfirstEdge : 8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned) by lia.
  assert (Hnextaddr : 0 <= edge - 8 * (2 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hnextptr : Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + rc / 64)))
      (Ptrofs.repr (8 * (1 - 0 / 64))) = Ptrofs.repr (edge - 8 * (2 + rc / 64))).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by exact Hsrcaddr.
    change (8 * (1 - 0 / 64)) with 8. change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. f_equal; lia. }
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
  assert (HnextP : Mem.load Mint64 mp bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next)).
  { erewrite Mem.load_store_other; [|exact SP|exact Hsepnext].
    erewrite Mem.load_store_other; [exact Hnext|exact SC|exact Hsepnext]. }
  assert (PWlowP : Mem.valid_access mp Mint64 bw (write_word_address outedge cursor - 8) Writable).
  { eapply Mem.store_valid_access_1; [exact SP|].
    eapply Mem.store_valid_access_1; [exact SC|exact PWlow]. }
  destruct (memcpy_word_effect Hmodel mp bi (edge - 8 * (2 + rc / 64)) bw
    (write_word_address outedge cursor - 8) next HnextP PWlowP Hnextaddr Hlowaddr Hsepnextlow)
    as (mf & Hext & Hword & Hother & Hperm & Hvalid).
  assert (Hss : 64 - rc mod 64 = cursor mod 64) by lia.
  exists mf. split.
  - assert (HAmax : write_word_address outedge cursor <= Ptrofs.max_unsigned) by lia.
    eapply eval_copy_helper_prefix_composes with (out := Out_normal); try eassumption; [|left; reflexivity].
    eapply exec_copy_tail_memcpy_equal with
      (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
      (dst_ofs := Ptrofs.repr (write_word_address outedge cursor)) (mc := mc) (mp := mp)
      (bi := bi) (bw := bw) (ds := cursor mod 64) (n := n) (old := old) (source := source); try lia.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss. rewrite Hss. reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env, copy_frame_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact Hold.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SC.
    + rewrite Ptrofs.unsigned_repr by exact Hsrcaddr; exact HsourceC.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr. rewrite Hss in SP. exact SP.
    + rewrite Hlowptr, Hnextptr. exact Hext.
  - split.
    + rewrite Hother; [|right; right; change (write_word_address outedge cursor - 8 + 8 <= write_word_address outedge cursor); lia].
      exact (Mem.load_store_same _ _ _ _ _ _ SP).
    + split; [exact Hword|]. split.
      * destruct HW as [Hedge Hcursor]. split.
        -- rewrite Hother by (left; exact Hbd).
           erewrite Mem.load_store_other; [|exact SP|auto].
           erewrite Mem.load_store_other; [exact Hedge|exact SC|auto].
        -- rewrite Hother by (left; exact Hbd).
           erewrite Mem.load_store_other; [|exact SP|auto].
           erewrite Mem.load_store_other; [exact Hcursor|exact SC|auto].
      * split.
        -- intros chunk b ofs Houtside.
           assert (HH : b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
               write_word_address outedge cursor + 8 <= ofs) by (intuition lia).
           rewrite Hother by (intuition lia).
           erewrite Mem.load_store_other; [|exact SP|exact HH].
           eapply Mem.load_store_other; [exact SC|exact HH].
        -- split.
           ++ intros b ofs kind p HP. apply Hperm. eauto using Mem.perm_store_1.
           ++ intros b HV. apply Hvalid. eauto using Mem.store_valid_block_1.
Qed.

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

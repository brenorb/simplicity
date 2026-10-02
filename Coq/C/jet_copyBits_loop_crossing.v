(** The actual second return of the first copyBitsHelper loop iteration.
    The input crosses a word, and the destination receives one full word.
    Raw lemmas are INTERNAL; the initial-only theorem derives their stores. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_read8_layout C.jet_write_layout C.jet_copyBits_exec.
Require Import C.jet_copyBits_helper_exec C.jet_copyBits_loop_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition copy_loop_join := Ssequence (Sset _t'5 (copy_word _dst_ptr))
  (Ssequence (Sset _t'6 (Ederef (Ebinop Osub (Etempvar _src_ptr (tptr tulong))
    (Econst_int Int.one tint) (tptr tulong)) tulong))
    (Sassign (copy_word _dst_ptr) (Ebinop Oor (Etempvar _t'5 tulong)
      (Ecast (Ebinop Oshr (Etempvar _t'6 tulong) (Etempvar _src_shift tulong) tulong) tulong) tulong))).
Definition copy_loop_after_full :=
  match copy_loop_after_short with Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Lemma copy_loop_after_short_shape : copy_loop_after_short = Ssequence copy_loop_join
  (Ssequence (Sifthenelse (Ebinop Ole (Etempvar _n tulong) generated_uword_bits tint)
    (Sreturn None) Sskip) copy_loop_after_full).
Proof. reflexivity. Qed.

Definition copy_loop_join_value ss source next :=
  Int64.or (copy_loop_value ss source) (Int64.shru next (Int64.repr ss)).
Definition copy_loop_join_env le ss source next :=
  PTree.set _t'6 (Vlong next) (PTree.set _t'5 (Vlong (copy_loop_value ss source)) le).

Lemma exec_copy_loop_join le m mf bi src_ofs bw dst_ofs ss source next :
  1 <= ss <= 63 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong (copy_loop_value ss source)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_join_value ss source next)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop_join E0
    (copy_loop_join_env le ss source next) mf Out_normal.
Proof.
  intros Hss HP HD HS Hdest Hnext SF.
  assert (Hshift : Int64.ltu (Int64.repr ss) Int64.iwordsize = Datatypes.true).
  { unfold Int64.ltu. rewrite Int64.unsigned_repr by (change (0 <= ss <= 18446744073709551615); lia).
    change ((if zlt ss 64 then true else false) = true). rewrite zlt_true by lia; reflexivity. }
  unfold copy_loop_join, copy_loop_join_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'5 (Vlong (copy_loop_value ss source)) le).
  - apply exec_set. eapply copy_eval_word; [exact HD|exact Hdest].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'6 (Vlong next) (PTree.set _t'5 (Vlong (copy_loop_value ss source)) le)).
    + apply exec_set. eapply eval_Elvalue.
      * eapply eval_Ederef. eapply eval_Ebinop with (v1 := Vptr bi src_ofs) (v2 := Vint Int.one).
        -- copy_temp.
        -- apply eval_Econst_int.
        -- copy_scalar.
      * apply deref_loc_value with (chunk := Mint64); [reflexivity|exact Hnext].
    + eapply exec_Sassign_value with (v := Vlong (copy_loop_join_value ss source next))
        (v2 := Vlong (copy_loop_join_value ss source next)).
      * eapply eval_Ederef. copy_temp.
      * unfold copy_loop_join_value. copy_expr.
      * reflexivity.
      * apply assign_frame_word_at; exact SF.
Qed.

Lemma exec_copy_loop_full le m mi mf bi src_ofs bw dst_ofs ss n source next :
  1 <= ss <= 63 -> ss < n <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_value ss source)) = Some mi ->
  Mem.load Mint64 mi bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 mi bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_join_value ss source next)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop E0
    (copy_loop_join_env (copy_loop_env le ss source) ss source next) mf (Out_return None).
Proof.
  intros Hss Hn HP HD HS HN Hsource SI Hnext SF.
  assert (Hback : Int64.ltu (Int64.repr ss) (Int64.repr n) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  assert (Hfull : Int64.ltu (Int64.repr 64) (Int64.repr n) = Datatypes.false).
  { unfold Int64.ltu. change (Int64.unsigned (Int64.repr 64)) with 64.
    rewrite Int64.unsigned_repr by (change (0 <= n <= 18446744073709551615); lia).
    change ((if zlt 64 n then true else false) = false). rewrite zlt_false by lia; reflexivity. }
  rewrite copy_loop_shape. eapply exec_Sloop_stop1 with (out' := Out_return None); [|constructor].
  rewrite copy_loop_body_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le); [apply exec_Sskip|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := copy_loop_env le ss source).
  - eapply exec_copy_loop_fill; eassumption.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := copy_loop_env le ss source).
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ss)).
        -- unfold copy_loop_env; copy_temp.
        -- unfold copy_loop_env; copy_temp.
        -- change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ss) (Int64.repr n)))) = Some (Vint Int.zero)).
           rewrite Hback; reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + rewrite copy_loop_after_short_shape.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf)
        (le1 := copy_loop_join_env (copy_loop_env le ss source) ss source next).
      * eapply exec_copy_loop_join with (src_ofs := src_ofs) (dst_ofs := dst_ofs); try eassumption.
        -- unfold copy_loop_env; rewrite !PTree.gso by discriminate; exact HP.
        -- unfold copy_loop_env; rewrite !PTree.gso by discriminate; exact HD.
        -- unfold copy_loop_env; rewrite !PTree.gso by discriminate; exact HS.
        -- exact (Mem.load_store_same _ _ _ _ _ _ SI).
      * apply exec_Sseq_2; [|discriminate].
        eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr 64)).
           ++ unfold copy_loop_join_env, copy_loop_env; copy_temp.
           ++ apply eval_generated_uword_bits.
           ++ change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr 64) (Int64.repr n)))) = Some (Vint Int.one)).
              rewrite Hfull; reflexivity.
        -- reflexivity.
        -- apply exec_Sreturn_none.
Qed.

Lemma exec_copy_choice_from_loop le le' m mf ss :
  1 <= ss <= 63 -> le!_src_shift = Some (Vlong (Int64.repr ss)) ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop E0 le' mf (Out_return None) ->
  Clight2.exec_stmt ge0 empty_env le m copy_tail_after_partial E0 le' mf (Out_return None).
Proof.
  intros Hss HS Hloop.
  assert (Hmod : Int64.modu (Int64.repr ss) (Int64.repr 64) = Int64.repr ss).
  { unfold Int64.modu. rewrite Int64.unsigned_repr by (change (0 <= ss <= 18446744073709551615); lia).
    change (Int64.repr (ss mod 64) = Int64.repr ss). rewrite Z.mod_small by lia; reflexivity. }
  assert (Hnonzero : Int64.eq Int64.zero (Int64.repr ss) = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ss <= 18446744073709551615); lia).
    change (0 = ss) in HE; lia. }
  rewrite copy_tail_choice_shape.
  eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
  - eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong (Int64.repr ss)).
    + apply eval_Econst_int.
    + eapply eval_Ebinop; [copy_temp|apply eval_generated_uword_bits|copy_scalar].
    + change (Some (Val.of_bool (Int64.eq Int64.zero (Int64.repr ss))) = Some (Vint Int.zero)).
      rewrite Hnonzero; reflexivity.
  - reflexivity.
  - exact Hloop.
Qed.

Theorem eval_copy_helper_aligned_full m bd base bs sbase bi edge rc bw outedge cursor n source next :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (2 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < rc mod 64 -> cursor mod 64 = 0 -> 64 - rc mod 64 < n <= 64 -> n <= cursor ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (2 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_loop_join_value (64 - rc mod 64) source next)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hsrc Hdst Hn Hnc Hbd Hsep Hsource Hnext PW.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  assert (HfirstEdge : 8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned) by lia.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hnextaddr : 0 <= edge - 8 * (2 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hnextptr : Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + rc / 64))) (Ptrofs.repr 8) =
      Ptrofs.repr (edge - 8 * (2 + rc / 64))).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by exact Hsrcaddr.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. f_equal; lia. }
  assert (Hdstaddr : 0 <= write_word_address outedge cursor <= Ptrofs.max_unsigned).
  { unfold write_word_address in *. pose proof (Z.div_pos (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
  destruct (Mem.valid_access_store m Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_loop_value (64 - rc mod 64) source)) PW) as [mi SI].
  assert (HnextI : Mem.load Mint64 mi bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next)).
  { erewrite Mem.load_store_other; [exact Hnext|exact SI|exact Hsep]. }
  assert (PWI : Mem.valid_access mi Mint64 bw (write_word_address outedge cursor) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mi Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_loop_join_value (64 - rc mod 64) source next)) PWI) as [mf SF].
  exists mf. split.
  - eapply eval_copy_helper_prefix_composes; try eassumption; [|right; reflexivity].
    rewrite copy_helper_tail_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := copy_helper_env bd base bs sbase n bi edge rc bw outedge cursor).
    + eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := Datatypes.false).
      * apply eval_Etempvar. unfold copy_helper_env, copy_dst_shift_env.
        rewrite PTree.gss, Hdst; reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + eapply exec_copy_choice_from_loop with (ss := 64 - rc mod 64); [lia| |].
      * unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * eapply exec_copy_loop_full with (bi := bi) (bw := bw) (mi := mi)
          (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
          (dst_ofs := Ptrofs.repr (write_word_address outedge cursor))
          (ss := 64 - rc mod 64) (n := n) (source := source) (next := next); try lia.
        -- unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env, copy_frame_env.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- rewrite Ptrofs.unsigned_repr by exact Hsrcaddr; exact Hsource.
        -- rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SI.
        -- rewrite Hnextptr, Ptrofs.unsigned_repr by exact Hnextaddr; exact HnextI.
        -- rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SF.
  - split.
    + exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * destruct HW as [Hedge Hcursor]. split.
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           erewrite Mem.load_store_other; [exact Hedge|exact SI|auto].
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           erewrite Mem.load_store_other; [exact Hcursor|exact SI|auto].
      * split.
        -- intros chunk b ofs Houtside.
           erewrite Mem.load_store_other; [|exact SF|exact Houtside].
           eapply Mem.load_store_other; eauto.
        -- split.
           ++ intros b ofs kind p HP; eauto using Mem.perm_store_1.
           ++ intros b HV; eauto using Mem.store_valid_block_1.
Qed.

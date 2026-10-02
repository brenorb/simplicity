(** Execute the actual first loop return in copyBitsHelper. The caller may
    enter this loop after a partial-word fill or with an aligned destination.
    No external memcpy behavior is assumed and no public jet is counted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_read8_layout C.jet_write_layout C.jet_copyBits_exec.
Require Import C.jet_LSBkeep_width C.jet_copyBits_helper_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition copy_memcpy_branch :=
  match copy_tail_after_partial with Sifthenelse _ yes _ => yes | _ => Sskip end.
Definition copy_loop :=
  match copy_tail_after_partial with Sifthenelse _ _ no => no | _ => Sskip end.
Definition copy_loop_body :=
  match copy_loop with Sloop body _ => body | _ => Sskip end.
Definition copy_loop_after_short :=
  match copy_loop_body with Ssequence _ (Ssequence _ (Ssequence _ rest)) => rest | _ => Sskip end.
Definition copy_loop_fill := Ssequence
  (Ssequence (Sset _t'7 (copy_word _src_ptr))
    (Scall (Some _t'4) (Evar _LSBkeep (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      [Etempvar _t'7 tulong; Etempvar _src_shift tulong]))
  (Sassign (copy_word _dst_ptr) (Ecast (Ebinop Oshl (Etempvar _t'4 tulong)
    (Ebinop Osub generated_uword_bits (Etempvar _src_shift tulong) tulong) tulong) tulong)).

Lemma copy_tail_choice_shape : copy_tail_after_partial = Sifthenelse
  (Ebinop Oeq (Econst_int Int.zero tint)
    (Ebinop Omod (Etempvar _src_shift tulong) generated_uword_bits tulong) tint)
  copy_memcpy_branch copy_loop.
Proof. reflexivity. Qed.
Lemma copy_loop_shape : copy_loop = Sloop copy_loop_body Sskip.
Proof. reflexivity. Qed.
Lemma copy_loop_body_shape : copy_loop_body = Ssequence Sskip
  (Ssequence copy_loop_fill (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _n tulong) (Etempvar _src_shift tulong) tint)
      (Sreturn None) Sskip) copy_loop_after_short)).
Proof. reflexivity. Qed.

Definition copy_loop_value ss source :=
  Int64.shl (Int64.zero_ext ss source) (Int64.repr (64 - ss)).
Definition copy_loop_env le ss source :=
  PTree.set _t'4 (Vlong (Int64.zero_ext ss source)) (PTree.set _t'7 (Vlong source) le).

Lemma exec_copy_loop_fill le m mf bi src_ofs bw dst_ofs ss source :
  1 <= ss <= 63 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_value ss source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop_fill E0 (copy_loop_env le ss source) mf Out_normal.
Proof.
  intros Hss HP HD HS Hsource SF.
  assert (Hsub : Int64.sub (Int64.repr 64) (Int64.repr ss) = Int64.repr (64 - ss)).
  { unfold Int64.sub. change (Int64.unsigned (Int64.repr 64)) with 64.
    rewrite Int64.unsigned_repr; [reflexivity|change (0 <= ss <= 18446744073709551615); lia]. }
  assert (Hshift : Int64.ltu (Int64.repr (64 - ss)) Int64.iwordsize = Datatypes.true).
  { unfold Int64.ltu. rewrite Int64.unsigned_repr by (change (0 <= 64 - ss <= 18446744073709551615); lia).
    change ((if zlt (64 - ss) 64 then true else false) = true). rewrite zlt_true by lia; reflexivity. }
  unfold copy_loop_fill, copy_loop_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'4 (Vlong (Int64.zero_ext ss source)) (PTree.set _t'7 (Vlong source) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'7 (Vlong source) le).
    + apply exec_set. eapply copy_eval_word; [exact HP|exact Hsource].
    + eapply call_word_helper with (f := f_LSBkeep) (n := Int64.repr ss).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply symbol_LSBkeep.
      * apply funct_LSBkeep.
      * copy_temp.
      * copy_temp.
      * apply eval_keep_width; lia.
  - eapply exec_Sassign_value with (v := Vlong (copy_loop_value ss source))
      (v2 := Vlong (copy_loop_value ss source)).
    + eapply eval_Ederef. copy_temp.
    + unfold copy_loop_value. copy_expr.
    + reflexivity.
    + apply assign_frame_word_at; exact SF.
Qed.

Lemma exec_copy_loop_short le m mf bi src_ofs bw dst_ofs ss n source :
  1 <= ss <= 63 -> 0 < n <= ss ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_value ss source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop E0
    (copy_loop_env le ss source) mf (Out_return None).
Proof.
  intros Hss Hn HP HD HS HN Hsource SF.
  assert (Hback : Int64.ltu (Int64.repr ss) (Int64.repr n) = Datatypes.false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_false by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_loop_shape. eapply exec_Sloop_stop1 with (out' := Out_return None); [|constructor].
  rewrite copy_loop_body_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le); [apply exec_Sskip|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := copy_loop_env le ss source).
  - eapply exec_copy_loop_fill; eassumption.
  - apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ss)).
      * unfold copy_loop_env; copy_temp.
      * unfold copy_loop_env; copy_temp.
      * change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ss) (Int64.repr n)))) = Some (Vint Int.one)).
        rewrite Hback; reflexivity.
    + reflexivity.
    + apply exec_Sreturn_none.
Qed.

Lemma exec_copy_tail_aligned_short le m mf bi src_ofs bw dst_ofs ss n source :
  1 <= ss <= 63 -> 0 < n <= ss ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong Int64.zero) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_value ss source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0
    (copy_loop_env le ss source) mf (Out_return None).
Proof.
  intros Hss Hn HP HD HS HDS HN Hsource SF.
  assert (Hmod : Int64.modu (Int64.repr ss) (Int64.repr 64) = Int64.repr ss).
  { unfold Int64.modu. rewrite Int64.unsigned_repr by (change (0 <= ss <= 18446744073709551615); lia).
    change (Int64.repr (ss mod 64) = Int64.repr ss). rewrite Z.mod_small by lia; reflexivity. }
  assert (Hnonzero : Int64.eq Int64.zero (Int64.repr ss) = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ss <= 18446744073709551615); lia).
    change (0 = ss) in HE; lia. }
  rewrite copy_helper_tail_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
  - eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := Datatypes.false).
    + copy_temp.
    + reflexivity.
    + apply exec_Sskip.
  - rewrite copy_tail_choice_shape.
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong (Int64.repr ss)).
      * apply eval_Econst_int.
      * eapply eval_Ebinop; [copy_temp|apply eval_generated_uword_bits|copy_scalar].
      * change (Some (Val.of_bool (Int64.eq Int64.zero (Int64.repr ss))) = Some (Vint Int.zero)).
        rewrite Hnonzero; reflexivity.
    + reflexivity.
    + eapply exec_copy_loop_short; eassumption.
Qed.

Theorem eval_copy_helper_aligned_short m bd base bs sbase bi edge rc bw outedge cursor n source :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < rc mod 64 -> cursor mod 64 = 0 -> 0 < n <= 64 - rc mod 64 -> n <= cursor ->
  bd <> bw ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_loop_value (64 - rc mod 64) source)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hsrc Hdst Hn Hnc Hbd Hsource PW.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hdstaddr : 0 <= write_word_address outedge cursor <= Ptrofs.max_unsigned).
  { unfold write_word_address in *. pose proof (Z.div_pos (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
  destruct (Mem.valid_access_store m Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_loop_value (64 - rc mod 64) source)) PW) as [mf SF].
  exists mf. split.
  - eapply eval_copy_helper_prefix_composes; try eassumption; [|right; reflexivity].
    eapply exec_copy_tail_aligned_short with (bi := bi) (bw := bw)
      (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
      (dst_ofs := Ptrofs.repr (write_word_address outedge cursor))
      (ss := 64 - rc mod 64) (n := n) (source := source); try lia.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env. rewrite PTree.gss, Hdst; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env, copy_frame_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + rewrite Ptrofs.unsigned_repr by exact Hsrcaddr; exact Hsource.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SF.
  - split.
    + exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * destruct HW as [Hedge Hcursor]. split.
        -- erewrite Mem.load_store_other; [exact Hedge|exact SF|auto].
        -- erewrite Mem.load_store_other; [exact Hcursor|exact SF|auto].
      * split.
        -- intros chunk b ofs Houtside. eapply Mem.load_store_other; eauto.
        -- split.
           ++ intros b ofs kind p HP; eauto using Mem.perm_store_1.
           ++ intros b HV; eauto using Mem.store_valid_block_1.
Qed.

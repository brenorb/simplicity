(** Actual partial-destination continuation across an input-word boundary.
    Raw statement lemmas are INTERNAL; final helper contracts derive stores
    and preserved source loads from initial memory. No public jet coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_write_layout C.jet_copyBits_exec C.jet_copyBits_helper_exec.
Require Import C.jet_copyBits_helper_right C.jet_copyBits_short_word C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Lemma copy_left_after_return_shape : copy_left_after_return =
  Ssequence (Sset _n (Ebinop Osub (Etempvar _n tulong) (Etempvar _src_shift tulong) tulong))
    (Ssequence (Sset _dst_shift (Ebinop Osub (Etempvar _dst_shift tulong) (Etempvar _src_shift tulong) tulong))
      (Ssequence (Sset _src_ptr (Ebinop Osub (Etempvar _src_ptr (tptr tulong))
        (Econst_int Int.one tint) (tptr tulong))) (Sset _src_shift generated_uword_bits))).
Proof. reflexivity. Qed.

Definition copy_cross_env le bi src_ofs ss ds n :=
  PTree.set _src_shift (Vlong (Int64.repr 64))
    (PTree.set _src_ptr (Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr 8)))
      (PTree.set _dst_shift (Vlong (Int64.repr (ds - ss)))
        (PTree.set _n (Vlong (Int64.repr (n - ss))) le))).

Lemma exec_copy_left_advance le m bi src_ofs ss ds n :
  1 <= ss /\ ss < ds <= 63 -> ss < n <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) ->
  le!_dst_shift = Some (Vlong (Int64.repr ds)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  Clight2.exec_stmt ge0 empty_env le m copy_left_after_return E0
    (copy_cross_env le bi src_ofs ss ds n) m Out_normal.
Proof.
  intros Hr Hn HP HS HD HN.
  assert (Hsubn : Int64.sub (Int64.repr n) (Int64.repr ss) = Int64.repr (n - ss)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr;
      [reflexivity|change (0 <= ss <= 18446744073709551615); lia|
        change (0 <= n <= 18446744073709551615); lia]. }
  assert (Hsubd : Int64.sub (Int64.repr ds) (Int64.repr ss) = Int64.repr (ds - ss)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr;
      [reflexivity|change (0 <= ss <= 18446744073709551615); lia|
        change (0 <= ds <= 18446744073709551615); lia]. }
  rewrite copy_left_after_return_shape. unfold copy_cross_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _n (Vlong (Int64.repr (n - ss))) le).
  - apply exec_set. copy_expr.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _dst_shift (Vlong (Int64.repr (ds - ss)))
        (PTree.set _n (Vlong (Int64.repr (n - ss))) le)).
    + apply exec_set. copy_expr.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := PTree.set _src_ptr (Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr 8)))
          (PTree.set _dst_shift (Vlong (Int64.repr (ds - ss)))
            (PTree.set _n (Vlong (Int64.repr (n - ss))) le))).
      * apply exec_set. copy_expr.
      * apply exec_set. apply eval_generated_uword_bits.
Qed.

Lemma copy_left_low_clear ss ds old source :
  1 <= ss /\ ss < ds <= 63 ->
  clear_low (ds - ss) (copy_left_value ss ds old source) = copy_left_value ss ds old source.
Proof.
  intros Hr. apply Int64.same_bits_eq. intros i Hi. change (0 <= i < 64) in Hi.
  rewrite clear_low_bits by lia. destruct (zlt i (ds - ss)); [|reflexivity].
  rewrite copy_left_value_bits by lia. rewrite zlt_true by lia; reflexivity.
Qed.

Definition copy_partial_cross_value ss ds old source next :=
  copy_right_value 64 (ds - ss) (copy_left_value ss ds old source) next.
Definition copy_partial_cross_env le bi src_ofs ss ds n old source next :=
  copy_right_env (copy_cross_env (copy_left_env (copy_clear_env le ds old) ss ds old source)
    bi src_ofs ss ds n) 64 (ds - ss) (copy_left_value ss ds old source) next.

Lemma exec_copy_left_continue le m ml bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ss /\ ss < ds <= 63 -> ss < n <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong (clear_low ds old)) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_left_value ss ds old source)) = Some ml ->
  Clight2.exec_stmt ge0 empty_env le m copy_partial_left E0
    (copy_cross_env (copy_left_env le ss ds old source) bi src_ofs ss ds n) ml Out_normal.
Proof.
  intros Hr Hn HP HD HS HDS HN Hsource Hdest SL.
  assert (Hback : Int64.ltu (Int64.repr ss) (Int64.repr n) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_partial_left_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ml) (le1 := copy_left_env le ss ds old source).
  - eapply exec_copy_left_fill; eassumption.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ml) (le1 := copy_left_env le ss ds old source).
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ss)).
        -- unfold copy_left_env; copy_temp.
        -- unfold copy_left_env; copy_temp.
        -- change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ss) (Int64.repr n)))) = Some (Vint Int.zero)).
           rewrite Hback; reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + eapply exec_copy_left_advance; try eassumption;
        unfold copy_left_env; rewrite !PTree.gso by discriminate; assumption.
Qed.

(** INTERNAL: the common right fill and return, independent of its prefix. *)
Lemma exec_copy_right_short le m mf bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds <= ss <= 64 -> 0 < n <= ds ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong (clear_low ds old)) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ss ds old source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_partial_right E0
    (copy_right_env le ss ds old source) mf (Out_return None).
Proof.
  intros Hds Hss Hn HP HD HS HDS HN Hsource Hdest SF.
  assert (Hback : Int64.ltu (Int64.repr ds) (Int64.repr n) = Datatypes.false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_false by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ds <= 18446744073709551615); lia]. }
  rewrite copy_partial_right_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := copy_right_env le ss ds old source).
  - eapply exec_copy_right_fill; eassumption.
  - apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ds)).
      * unfold copy_right_env; copy_temp.
      * unfold copy_right_env; copy_temp.
      * change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ds) (Int64.repr n)))) = Some (Vint Int.one)).
        rewrite Hback; reflexivity.
    + reflexivity.
    + apply exec_Sreturn_none.
Qed.

Lemma exec_copy_tail_partial_cross le m mc ml mf bi src_ofs bw dst_ofs ss ds n old source next :
  1 <= ss /\ ss < ds <= 63 -> ss < n <= ds ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_left_value ss ds old source)) = Some ml ->
  Mem.load Mint64 ml bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 ml bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_partial_cross_value ss ds old source next)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0
    (copy_partial_cross_env le bi src_ofs ss ds n old source next) mf (Out_return None).
Proof.
  intros Hr Hn HP HD HS HDS HN Hold SC Hsource SL Hnext SF.
  assert (Hnonzero : Int64.eq (Int64.repr ds) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ds <= 18446744073709551615); lia).
    change (ds = 0) in HE; lia. }
  assert (Hlt : Int64.ltu (Int64.repr ss) (Int64.repr ds) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_helper_tail_shape. apply exec_Sseq_2; [|discriminate].
  eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
  - copy_temp.
  - change (Some (negb (Int64.eq (Int64.repr ds) Int64.zero)) = Some true).
    rewrite Hnonzero; reflexivity.
  - rewrite copy_partial_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
    + eapply exec_copy_clear; eauto; lia.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ml)
        (le1 := copy_cross_env (copy_left_env (copy_clear_env le ds old) ss ds old source) bi src_ofs ss ds n).
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr ds)).
           ++ unfold copy_clear_env; copy_temp.
           ++ unfold copy_clear_env; copy_temp.
           ++ change (Some (Val.of_bool (Int64.ltu (Int64.repr ss) (Int64.repr ds))) = Some (Vint Int.one)).
              rewrite Hlt; reflexivity.
        -- reflexivity.
        -- eapply exec_copy_left_continue with (src_ofs := src_ofs) (dst_ofs := dst_ofs)
             (ss := ss) (ds := ds) (n := n) (old := old) (source := source); try eassumption; try lia.
           ++ unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HP.
           ++ unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HD.
           ++ unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HS.
           ++ unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HDS.
           ++ unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HN.
           ++ exact (Mem.load_store_same _ _ _ _ _ _ SC).
      * unfold copy_partial_cross_env. eapply exec_copy_right_short with
          (bi := bi) (src_ofs := Ptrofs.sub src_ofs (Ptrofs.repr 8))
          (bw := bw) (dst_ofs := dst_ofs) (ss := 64) (ds := ds - ss) (n := n - ss)
          (old := copy_left_value ss ds old source) (source := next); try lia.
        -- unfold copy_cross_env; rewrite !PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
        -- unfold copy_cross_env, copy_left_env, copy_clear_env;
             rewrite !PTree.gso by discriminate; exact HD.
        -- unfold copy_cross_env; rewrite PTree.gss; reflexivity.
        -- unfold copy_cross_env; rewrite !PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
        -- unfold copy_cross_env; rewrite !PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
        -- exact Hnext.
        -- rewrite copy_left_low_clear by exact Hr. exact (Mem.load_store_same _ _ _ _ _ _ SL).
        -- exact SF.
Qed.

Theorem eval_copy_helper_partial_cross m bd base bs sbase bi edge rc bw outedge cursor n old source next :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (2 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  64 - rc mod 64 < n <= cursor mod 64 ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  (bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (2 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 m bw (write_word_address outedge cursor) = Some (Vlong old) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hn Hbd Hsep Hsepnext Hsource Hnext Hold PW.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
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
    (Vlong (clear_low (cursor mod 64) old)) PW) as [mc SC].
  assert (HsourceC : Mem.load Mint64 mc bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source)).
  { erewrite Mem.load_store_other; [exact Hsource|exact SC|exact Hsep]. }
  assert (PWC : Mem.valid_access mc Mint64 bw (write_word_address outedge cursor) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mc Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_left_value (64 - rc mod 64) (cursor mod 64) old source)) PWC) as [ml SL].
  assert (HnextL : Mem.load Mint64 ml bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next)).
  { erewrite Mem.load_store_other; [|exact SL|exact Hsepnext].
    erewrite Mem.load_store_other; [exact Hnext|exact SC|exact Hsepnext]. }
  assert (PWL : Mem.valid_access ml Mint64 bw (write_word_address outedge cursor) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store ml Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) PWL) as [mf SF].
  exists mf. split.
  - eapply eval_copy_helper_prefix_composes; try eassumption; [|right; reflexivity].
    eapply exec_copy_tail_partial_cross with
      (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
      (dst_ofs := Ptrofs.repr (write_word_address outedge cursor)) (mc := mc) (ml := ml)
      (bi := bi) (bw := bw) (ss := 64 - rc mod 64) (ds := cursor mod 64)
      (n := n) (old := old) (source := source) (next := next); try lia.
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
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SL.
    + rewrite Hnextptr, Ptrofs.unsigned_repr by exact Hnextaddr; exact HnextL.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SF.
  - split; [exact (Mem.load_store_same _ _ _ _ _ _ SF)|]. split.
    + destruct HW as [Hedge Hcursor]. split.
      * erewrite Mem.load_store_other; [|exact SF|auto].
        erewrite Mem.load_store_other; [|exact SL|auto].
        erewrite Mem.load_store_other; [exact Hedge|exact SC|auto].
      * erewrite Mem.load_store_other; [|exact SF|auto].
        erewrite Mem.load_store_other; [|exact SL|auto].
        erewrite Mem.load_store_other; [exact Hcursor|exact SC|auto].
    + split.
      * intros chunk b ofs Houtside.
        erewrite Mem.load_store_other; [|exact SF|exact Houtside].
        erewrite Mem.load_store_other; [|exact SL|exact Houtside].
        eapply Mem.load_store_other; eauto.
      * split.
        -- intros b ofs kind p HP; eauto using Mem.perm_store_1.
        -- intros b HV; eauto using Mem.store_valid_block_1.
Qed.

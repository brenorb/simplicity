(** The actual partial-word copy path when the source has enough bits.
    Short-return helper contracts only; no public jet coverage is claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_read8_layout C.jet_write_layout C.jet_copyBits_exec.
Require Import C.jet_LSBclear_width C.jet_LSBkeep_width C.jet_word_bits.
Require Import C.jet_copyBits_helper_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition copy_right_fill := Ssequence
  (Ssequence (Sset _t'9 (copy_word _src_ptr))
    (Scall (Some _t'3) (Evar _LSBkeep (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      [Ecast (Ebinop Oshr (Etempvar _t'9 tulong)
        (Ebinop Osub (Etempvar _src_shift tulong) (Etempvar _dst_shift tulong) tulong) tulong) tulong;
        Etempvar _dst_shift tulong]))
  (Ssequence (Sset _t'8 (copy_word _dst_ptr))
    (Sassign (copy_word _dst_ptr) (Ebinop Oor (Etempvar _t'8 tulong) (Etempvar _t'3 tulong) tulong))).
Definition copy_right_after_return :=
  match copy_partial_right with Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Lemma copy_partial_right_shape : copy_partial_right = Ssequence copy_right_fill
  (Ssequence (Sifthenelse
    (Ebinop Ole (Etempvar _n tulong) (Etempvar _dst_shift tulong) tint) (Sreturn None) Sskip)
    copy_right_after_return).
Proof. reflexivity. Qed.

Definition copy_right_payload ss ds source :=
  Int64.zero_ext ds (Int64.shru source (Int64.repr (ss - ds))).
Definition copy_right_value ss ds old source :=
  Int64.or (clear_low ds old) (copy_right_payload ss ds source).
Definition copy_right_env le ss ds old source :=
  PTree.set _t'8 (Vlong (clear_low ds old))
    (PTree.set _t'3 (Vlong (copy_right_payload ss ds source)) (PTree.set _t'9 (Vlong source) le)).

Lemma exec_copy_right_fill le m mf bi src_ofs bw dst_ofs ss ds old source :
  1 <= ds <= 63 -> ds <= ss <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong (clear_low ds old)) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ss ds old source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_right_fill E0 (copy_right_env le ss ds old source) mf Out_normal.
Proof.
  intros Hds Hss HP HD HS HDS Hsource Hdest SF.
  assert (Hsub : Int64.sub (Int64.repr ss) (Int64.repr ds) = Int64.repr (ss - ds)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr;
      [reflexivity|change (0 <= ds <= 18446744073709551615); lia|change (0 <= ss <= 18446744073709551615); lia]. }
  assert (Hshift : Int64.ltu (Int64.repr (ss - ds)) Int64.iwordsize = Datatypes.true).
  { unfold Int64.ltu. rewrite Int64.unsigned_repr by (change (0 <= ss - ds <= 18446744073709551615); lia).
    change ((if zlt (ss - ds) 64 then true else false) = true). rewrite zlt_true by lia; reflexivity. }
  unfold copy_right_fill, copy_right_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'3 (Vlong (copy_right_payload ss ds source)) (PTree.set _t'9 (Vlong source) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'9 (Vlong source) le).
    + apply exec_set. eapply copy_eval_word; [exact HP|exact Hsource].
    + eapply call_word_helper with (f := f_LSBkeep) (n := Int64.repr ds)
        (w := Int64.shru source (Int64.repr (ss - ds))).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply symbol_LSBkeep.
      * apply funct_LSBkeep.
      * copy_expr.
      * copy_temp.
      * apply eval_keep_width; lia.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'8 (Vlong (clear_low ds old))
        (PTree.set _t'3 (Vlong (copy_right_payload ss ds source)) (PTree.set _t'9 (Vlong source) le))).
    + apply exec_set. eapply copy_eval_word; [|exact Hdest].
      rewrite !PTree.gso by discriminate; exact HD.
    + eapply exec_Sassign_value with (v := Vlong (copy_right_value ss ds old source))
        (v2 := Vlong (copy_right_value ss ds old source)).
      * eapply eval_Ederef. copy_temp.
      * unfold copy_right_value. copy_expr.
      * reflexivity.
      * apply assign_frame_word_at; exact SF.
Qed.

Lemma exec_copy_tail_short_right le m mc mf bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds <= ss <= 64 -> 0 < n <= ds ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ss ds old source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0
    (copy_right_env (copy_clear_env le ds old) ss ds old source) mf (Out_return None).
Proof.
  intros Hds Hss HN HP HD HS HDS HNtemp Hold SC Hsource SF.
  assert (Hnonzero : Int64.eq (Int64.repr ds) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ds <= 18446744073709551615); lia).
    change (ds = 0) in HE; lia. }
  assert (Hlt : Int64.ltu (Int64.repr ss) (Int64.repr ds) = Datatypes.false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_false by lia; reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  assert (Hback : Int64.ltu (Int64.repr ds) (Int64.repr n) = Datatypes.false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_false by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ds <= 18446744073709551615); lia]. }
  rewrite copy_helper_tail_shape. apply exec_Sseq_2; [|discriminate].
  eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
  - copy_temp.
  - change (Some (negb (Int64.eq (Int64.repr ds) Int64.zero)) = Some true).
    rewrite Hnonzero; reflexivity.
  - rewrite copy_partial_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
    + eapply exec_copy_clear; eauto; lia.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
      * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr ds)).
           ++ unfold copy_clear_env; copy_temp.
           ++ unfold copy_clear_env; copy_temp.
           ++ change (Some (Val.of_bool (Int64.ltu (Int64.repr ss) (Int64.repr ds))) = Some (Vint Int.zero)).
              rewrite Hlt; reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
      * rewrite copy_partial_right_shape.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf)
          (le1 := copy_right_env (copy_clear_env le ds old) ss ds old source).
        -- eapply exec_copy_right_fill with (src_ofs := src_ofs) (dst_ofs := dst_ofs); try eassumption.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HP.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HD.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HS.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HDS.
           ++ exact (Mem.load_store_same _ _ _ _ _ _ SC).
        -- apply exec_Sseq_2; [|discriminate].
           eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ds)).
              ** unfold copy_right_env, copy_clear_env; copy_temp.
              ** unfold copy_right_env, copy_clear_env; copy_temp.
              ** change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ds) (Int64.repr n)))) =
                   Some (Vint Int.one)). rewrite Hback; reflexivity.
           ++ reflexivity.
           ++ apply exec_Sreturn_none.
Qed.

Theorem eval_copy_helper_short_right m bd base bs sbase bi edge rc bw outedge cursor n old source :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < cursor mod 64 -> cursor mod 64 <= 64 - rc mod 64 -> 0 < n <= cursor mod 64 ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bw (write_word_address outedge cursor) = Some (Vlong old) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hpartial Hshort Hn Hbd Hsep Hsource Hold PW.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hdstaddr : 0 <= write_word_address outedge cursor <= Ptrofs.max_unsigned).
  { unfold write_word_address in *. pose proof (Z.div_pos (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
  eapply eval_copy_helper_partial_from_tail with (bi := bi) (edge := edge) (rc := rc)
    (old := old) (source := source); try eassumption.
  intros mc mf HsourceC SC SF.
  eexists; exists (Out_return None). split; [|right; reflexivity].
  eapply exec_copy_tail_short_right with (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
    (dst_ofs := Ptrofs.repr (write_word_address outedge cursor)) (mc := mc)
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
  + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SF.

Qed.

(** Partial-destination prefix of copyBitsHelper for copy counts above one
    word.  These are the statements of the existing internal prefix lemmas with
    the bound on the remaining count relaxed; the proofs are unchanged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_constants C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Require Import C.jet_copyBits_partial_crossing C.jet_copyBits_right_advance.
Require Import C.jet_copyBits_two_words_right_exec C.jet_copyBits_two_words_left_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 30.

Lemma exec_copy_right_advance_w le m bw dst_ofs ss ds n :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds < n <= 4096 ->
  le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) ->
  le!_dst_shift = Some (Vlong (Int64.repr ds)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  Clight2.exec_stmt ge0 empty_env le m copy_right_after_return E0
    (copy_right_advance_env le bw dst_ofs ss ds n) m Out_normal.
Proof.
  intros Hds Hss Hn HP HS HD HN.
  assert (Hsubn : Int64.sub (Int64.repr n) (Int64.repr ds) = Int64.repr (n - ds)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr;
      [reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= n <= 18446744073709551615); lia]. }
  assert (Hsubs : Int64.sub (Int64.repr ss) (Int64.repr ds) = Int64.repr (ss - ds)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr;
      [reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_right_after_return_shape. unfold copy_right_advance_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _n (Vlong (Int64.repr (n - ds))) le).
  - apply exec_set. copy_expr.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _src_shift (Vlong (Int64.repr (ss - ds)))
        (PTree.set _n (Vlong (Int64.repr (n - ds))) le)).
    + apply exec_set. copy_expr.
    + apply exec_set. copy_expr.
Qed.

Lemma exec_copy_right_continue_w le m mf bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds < n <= 4096 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong (clear_low ds old)) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ss ds old source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_partial_right E0
    (copy_right_advance_env (copy_right_env le ss ds old source) bw dst_ofs ss ds n) mf Out_normal.
Proof.
  intros Hds Hss Hn HP HD HS HDS HN Hsource Hdest SF.
  assert (Hback : Int64.ltu (Int64.repr ds) (Int64.repr n) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ds <= 18446744073709551615); lia]. }
  rewrite copy_partial_right_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := copy_right_env le ss ds old source).
  - eapply exec_copy_right_fill; eassumption.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := copy_right_env le ss ds old source).
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ds)).
        -- unfold copy_right_env; copy_temp.
        -- unfold copy_right_env; copy_temp.
        -- change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ds) (Int64.repr n)))) = Some (Vint Int.zero)).
           rewrite Hback; reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + eapply exec_copy_right_advance_w; try eassumption;
        unfold copy_right_env; rewrite !PTree.gso by discriminate; assumption.
Qed.

Lemma exec_copy_left_advance_w le m bi src_ofs ss ds n :
  1 <= ss /\ ss < ds <= 63 -> ss < n <= 4096 ->
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

Lemma exec_copy_left_continue_w le m ml bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ss /\ ss < ds <= 63 -> ss < n <= 4096 ->
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
    + eapply exec_copy_left_advance_w; try eassumption;
        unfold copy_left_env; rewrite !PTree.gso by discriminate; assumption.
Qed.

Lemma exec_copy_partial_continue_right_w le m mc mp bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds < n <= 4096 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ss ds old source)) = Some mp ->
  Clight2.exec_stmt ge0 empty_env le m copy_partial E0
    (copy_two_right_env le bw dst_ofs ss ds n old source) mp Out_normal.
Proof.
  intros Hds Hss Hn HP HD HS HDS HN Hold SC Hsource SP.
  assert (Hlt : Int64.ltu (Int64.repr ss) (Int64.repr ds) = Datatypes.false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_false by lia; reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_partial_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
  - eapply exec_copy_clear; eauto; lia.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr ds)).
        -- unfold copy_clear_env; copy_temp.
        -- unfold copy_clear_env; copy_temp.
        -- change (Some (Val.of_bool (Int64.ltu (Int64.repr ss) (Int64.repr ds))) = Some (Vint Int.zero)).
           rewrite Hlt; reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + unfold copy_two_right_env.
      eapply exec_copy_right_continue_w with (bi := bi) (src_ofs := src_ofs) (bw := bw)
        (dst_ofs := dst_ofs) (ss := ss) (ds := ds) (n := n) (old := old) (source := source); try eassumption.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HP.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HD.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HS.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HDS.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HN.
      * exact (Mem.load_store_same _ _ _ _ _ _ SC).
Qed.

Lemma exec_copy_partial_continue_left_w le m mc ml mp bi src_ofs bw dst_ofs ss ds n old source next :
  1 <= ss /\ ss < ds <= 63 -> ds < n <= 4096 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_left_value ss ds old source)) = Some ml ->
  Mem.load Mint64 ml bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 ml bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_partial_cross_value ss ds old source next)) = Some mp ->
  Clight2.exec_stmt ge0 empty_env le m copy_partial E0
    (copy_two_left_env le bi src_ofs bw dst_ofs ss ds n old source next) mp Out_normal.
Proof.
  intros Hr Hn HP HD HS HDS HN Hold SC Hsource SL Hnext SP.
  assert (Hlt : Int64.ltu (Int64.repr ss) (Int64.repr ds) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_partial_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
  - eapply exec_copy_clear; eauto; lia.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ml)
      (le1 := copy_cross_env (copy_left_env (copy_clear_env le ds old) ss ds old source) bi src_ofs ss ds n).
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr ds)).
        -- unfold copy_clear_env; copy_temp.
        -- unfold copy_clear_env; copy_temp.
        -- change (Some (Val.of_bool (Int64.ltu (Int64.repr ss) (Int64.repr ds))) = Some (Vint Int.one)).
           rewrite Hlt; reflexivity.
      * reflexivity.
      * eapply exec_copy_left_continue_w with (src_ofs := src_ofs) (dst_ofs := dst_ofs)
          (ss := ss) (ds := ds) (n := n) (old := old) (source := source); try eassumption; try lia.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HP.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HD.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HS.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HDS.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HN.
        -- exact (Mem.load_store_same _ _ _ _ _ _ SC).
    + unfold copy_two_left_env, copy_partial_cross_env.
      eapply exec_copy_right_continue_w with (bi := bi)
        (src_ofs := Ptrofs.sub src_ofs (Ptrofs.repr 8)) (bw := bw) (dst_ofs := dst_ofs)
        (ss := 64) (ds := ds - ss) (n := n - ss)
        (old := copy_left_value ss ds old source) (source := next); try lia.
      * unfold copy_cross_env; rewrite !PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
      * unfold copy_cross_env, copy_left_env, copy_clear_env; rewrite !PTree.gso by discriminate; exact HD.
      * unfold copy_cross_env; rewrite PTree.gss; reflexivity.
      * unfold copy_cross_env; rewrite !PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
      * unfold copy_cross_env; rewrite !PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
      * exact Hnext.
      * rewrite copy_left_low_clear by exact Hr. exact (Mem.load_store_same _ _ _ _ _ _ SL).
      * exact SP.
Qed.

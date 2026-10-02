(** INTERNAL actual-statement composition when both source and destination
    cross a word and the initial source shift is smaller. Initial contracts
    must derive every intermediate load/store premise used here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Require Import C.jet_copyBits_partial_crossing C.jet_copyBits_right_advance.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition copy_two_left_env le bi src_ofs bw dst_ofs ss ds n old source next :=
  copy_right_advance_env (copy_partial_cross_env le bi src_ofs ss ds n old source next)
    bw dst_ofs 64 (ds - ss) (n - ss).

Lemma exec_copy_partial_continue_left le m mc ml mp bi src_ofs bw dst_ofs ss ds n old source next :
  1 <= ss /\ ss < ds <= 63 -> ds < n <= 64 ->
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
      * eapply exec_copy_left_continue with (src_ofs := src_ofs) (dst_ofs := dst_ofs)
          (ss := ss) (ds := ds) (n := n) (old := old) (source := source); try eassumption; try lia.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HP.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HD.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HS.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HDS.
        -- unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HN.
        -- exact (Mem.load_store_same _ _ _ _ _ _ SC).
    + unfold copy_two_left_env, copy_partial_cross_env.
      eapply exec_copy_right_continue with (bi := bi)
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

Lemma exec_copy_tail_two_left le m mc ml mp mf bi src_ofs bw dst_ofs ss ds n old source next :
  1 <= ss /\ ss < ds <= 63 -> ds < n <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_left_value ss ds old source)) = Some ml ->
  Mem.load Mint64 ml bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 ml bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_partial_cross_value ss ds old source next)) = Some mp ->
  Mem.load Mint64 mp bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 mp bw (Ptrofs.unsigned (Ptrofs.sub dst_ofs (Ptrofs.repr 8)))
    (Vlong (copy_loop_value (64 - (ds - ss)) next)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0
    (copy_loop_env (copy_two_left_env le bi src_ofs bw dst_ofs ss ds n old source next)
      (64 - (ds - ss)) next) mf (Out_return None).
Proof.
  intros Hr Hn HP HD HS HDS HN Hold SC Hsource SL Hnext SP HnextP SF.
  assert (Hnonzero : Int64.eq (Int64.repr ds) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ds <= 18446744073709551615); lia).
    change (ds = 0) in HE; lia. }
  rewrite copy_helper_tail_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mp)
    (le1 := copy_two_left_env le bi src_ofs bw dst_ofs ss ds n old source next).
  - eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
    + copy_temp.
    + change (Some (negb (Int64.eq (Int64.repr ds) Int64.zero)) = Some true).
      rewrite Hnonzero; reflexivity.
    + eapply exec_copy_partial_continue_left; eassumption.
  - eapply exec_copy_choice_from_loop with (ss := 64 - (ds - ss)); [lia| |].
    + unfold copy_two_left_env, copy_right_advance_env.
      rewrite PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + eapply exec_copy_loop_short with (bi := bi) (bw := bw)
        (src_ofs := Ptrofs.sub src_ofs (Ptrofs.repr 8))
        (dst_ofs := Ptrofs.sub dst_ofs (Ptrofs.repr 8))
        (ss := 64 - (ds - ss)) (n := n - ds) (source := next); try lia.
      * unfold copy_two_left_env, copy_right_advance_env, copy_partial_cross_env, copy_right_env, copy_cross_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * unfold copy_two_left_env, copy_right_advance_env. rewrite PTree.gss; reflexivity.
      * unfold copy_two_left_env, copy_right_advance_env.
        rewrite PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * unfold copy_two_left_env, copy_right_advance_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss.
        replace (n - ss - (ds - ss)) with (n - ds) by lia; reflexivity.
      * exact HnextP.
      * exact SF.
Qed.

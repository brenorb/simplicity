(** INTERNAL actual partial-destination prefix with enough source bits.
    The subsequent actual loop remains a premise here, to be derived by
    initial-only contracts for both of its return cases. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Require Import C.jet_copyBits_right_advance C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition copy_two_right_env le bw dst_ofs ss ds n old source :=
  copy_right_advance_env (copy_right_env (copy_clear_env le ds old) ss ds old source)
    bw dst_ofs ss ds n.

Lemma exec_copy_partial_continue_right le m mc mp bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds < n <= 64 ->
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
      eapply exec_copy_right_continue with (bi := bi) (src_ofs := src_ofs) (bw := bw)
        (dst_ofs := dst_ofs) (ss := ss) (ds := ds) (n := n) (old := old) (source := source); try eassumption.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HP.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HD.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HS.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HDS.
      * unfold copy_clear_env; rewrite !PTree.gso by discriminate; exact HN.
      * exact (Mem.load_store_same _ _ _ _ _ _ SC).
Qed.

Lemma exec_copy_tail_two_right le le' m mc mp mf bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds < ss <= 64 -> ds < n <= 64 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_right_value ss ds old source)) = Some mp ->
  Clight2.exec_stmt ge0 empty_env (copy_two_right_env le bw dst_ofs ss ds n old source)
    mp copy_loop E0 le' mf (Out_return None) ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0 le' mf (Out_return None).
Proof.
  intros Hds Hss Hn HP HD HS HDS HN Hold SC Hsource SP Hloop.
  assert (Hnonzero : Int64.eq (Int64.repr ds) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ds <= 18446744073709551615); lia).
    change (ds = 0) in HE; lia. }
  rewrite copy_helper_tail_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mp)
    (le1 := copy_two_right_env le bw dst_ofs ss ds n old source).
  - eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
    + copy_temp.
    + change (Some (negb (Int64.eq (Int64.repr ds) Int64.zero)) = Some true).
      rewrite Hnonzero; reflexivity.
    + eapply exec_copy_partial_continue_right; try eassumption; lia.
  - eapply exec_copy_choice_from_loop with (ss := ss - ds); [lia| |exact Hloop].
    unfold copy_two_right_env, copy_right_advance_env.
    rewrite PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
Qed.

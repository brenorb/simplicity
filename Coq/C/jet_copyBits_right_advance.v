(** INTERNAL continuation lemmas for the actual common partial-word suffix.
    These update temporaries, not stored frame fields. Initial-only helper
    contracts still need to derive subsequent loop loads/stores and framing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_constants C.jet_copyBits_helper_exec.
Require Import C.jet_copyBits_helper_right C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Lemma copy_right_after_return_shape : copy_right_after_return =
  Ssequence (Sset _n (Ebinop Osub (Etempvar _n tulong) (Etempvar _dst_shift tulong) tulong))
    (Ssequence (Sset _src_shift (Ebinop Osub (Etempvar _src_shift tulong) (Etempvar _dst_shift tulong) tulong))
      (Sset _dst_ptr (Ebinop Osub (Etempvar _dst_ptr (tptr tulong))
        (Econst_int Int.one tint) (tptr tulong)))).
Proof. reflexivity. Qed.

Definition copy_right_advance_env le bw dst_ofs ss ds n :=
  PTree.set _dst_ptr (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8)))
    (PTree.set _src_shift (Vlong (Int64.repr (ss - ds)))
      (PTree.set _n (Vlong (Int64.repr (n - ds))) le)).

Lemma exec_copy_right_advance le m bw dst_ofs ss ds n :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds < n <= 64 ->
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

Lemma exec_copy_right_continue le m mf bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds < n <= 64 ->
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
    + eapply exec_copy_right_advance; try eassumption;
        unfold copy_right_env; rewrite !PTree.gso by discriminate; assumption.
Qed.

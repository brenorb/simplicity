(** Loop iterations of copyBitsHelper that continue (more than one word still
    to copy), and the generic composition of an iteration with the rest of
    the loop.  INTERNAL: these compose statement executions only. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_constants C.jet_copyBits_helper_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 30.

Lemma copy_loop_after_full_shape : copy_loop_after_full =
  Ssequence (Sset _n (Ebinop Osub (Etempvar _n tulong) generated_uword_bits tulong))
    (Ssequence
      (Sset _dst_ptr (Ebinop Osub (Etempvar _dst_ptr (tptr tulong)) (Econst_int Int.one tint) (tptr tulong)))
      (Sset _src_ptr (Ebinop Osub (Etempvar _src_ptr (tptr tulong)) (Econst_int Int.one tint) (tptr tulong)))).
Proof. reflexivity. Qed.

Definition copy_loop_next_env le bi src_ofs bw dst_ofs n :=
  PTree.set _src_ptr (Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr 8)))
    (PTree.set _dst_ptr (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8)))
      (PTree.set _n (Vlong (Int64.repr (n - 64))) le)).

Lemma exec_copy_loop_advance le m bi src_ofs bw dst_ofs n :
  64 < n <= 4096 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop_after_full E0
    (copy_loop_next_env le bi src_ofs bw dst_ofs n) m Out_normal.
Proof.
  intros Hn HP HD HN.
  assert (Hsubn : Int64.sub (Int64.repr n) (Int64.repr 64) = Int64.repr (n - 64)).
  { unfold Int64.sub. change (Int64.unsigned (Int64.repr 64)) with 64.
    rewrite Int64.unsigned_repr; [reflexivity|change (0 <= n <= 18446744073709551615); lia]. }
  rewrite copy_loop_after_full_shape. unfold copy_loop_next_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _n (Vlong (Int64.repr (n - 64))) le).
  - apply exec_set. copy_expr.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _dst_ptr (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8)))
        (PTree.set _n (Vlong (Int64.repr (n - 64))) le)).
    + apply exec_set. copy_expr.
    + apply exec_set. copy_expr.
Qed.

(** One full loop iteration that does not return. *)
Lemma exec_copy_loop_iter le m mi mf bi src_ofs bw dst_ofs ss n source next :
  1 <= ss <= 63 -> 64 < n <= 4096 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_value ss source)) = Some mi ->
  Mem.load Mint64 mi bi (Ptrofs.unsigned (Ptrofs.sub src_ofs (Ptrofs.repr 8))) = Some (Vlong next) ->
  Mem.store Mint64 mi bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_loop_join_value ss source next)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop_body E0
    (copy_loop_next_env (copy_loop_join_env (copy_loop_env le ss source) ss source next)
      bi src_ofs bw dst_ofs n) mf Out_normal.
Proof.
  intros Hss Hn HP HD HS HN Hsource SI Hnext SF.
  assert (Hback : Int64.ltu (Int64.repr ss) (Int64.repr n) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  assert (Hfull : Int64.ltu (Int64.repr 64) (Int64.repr n) = Datatypes.true).
  { unfold Int64.ltu. change (Int64.unsigned (Int64.repr 64)) with 64.
    rewrite Int64.unsigned_repr by (change (0 <= n <= 18446744073709551615); lia).
    rewrite zlt_true by lia; reflexivity. }
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
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf)
          (le1 := copy_loop_join_env (copy_loop_env le ss source) ss source next).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr 64)).
              ** unfold copy_loop_join_env, copy_loop_env; copy_temp.
              ** apply eval_generated_uword_bits.
              ** change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr 64) (Int64.repr n)))) = Some (Vint Int.zero)).
                 rewrite Hfull; reflexivity.
           ++ reflexivity.
           ++ apply exec_Sskip.
        -- eapply exec_copy_loop_advance; [exact Hn| | |];
             unfold copy_loop_join_env, copy_loop_env; rewrite !PTree.gso by discriminate; assumption.
Qed.

Lemma exec_copy_loop_step le le1 le2 m m1 m2 out :
  Clight2.exec_stmt ge0 empty_env le m copy_loop_body E0 le1 m1 Out_normal ->
  Clight2.exec_stmt ge0 empty_env le1 m1 copy_loop E0 le2 m2 out ->
  Clight2.exec_stmt ge0 empty_env le m copy_loop E0 le2 m2 out.
Proof.
  intros HB HL. rewrite copy_loop_shape in *.
  eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0) (out1 := Out_normal)
    (le1 := le1) (m1 := m1) (le2 := le1) (m2 := m1).
  - exact HB.
  - constructor.
  - apply exec_Sskip.
  - exact HL.
Qed.

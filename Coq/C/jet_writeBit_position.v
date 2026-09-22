(** Actual carry-bit writes at any cursor in one backing word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_writeBit C.jets C.jet_word_bits
  C.jet_frame_arith C.jet_frame_constants C.jet_LSBclear_width.
Import Clightdefs Clightdefs.ClightNotations Values Mem Ctypes Events ListNotations.
Local Open Scope Z_scope.
Local Open Scope clight_scope.
Local Transparent Archi.ptr64.

Section Position.
Variable cursor : Z.
Hypothesis Hcursor : 1 <= cursor <= 64.

Lemma bitpos_index : Int64.divu (Int64.repr (cursor - 1)) (Int64.repr 64) = Int64.zero.
Proof.
  unfold Int64.divu. rewrite !cursor_unsigned by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma bitpos_remainder : Int64.modu (Int64.repr (cursor - 1)) (Int64.repr 64) =
  Int64.repr (cursor - 1).
Proof.
  unfold Int64.modu. rewrite !cursor_unsigned by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma bitpos_width : Int64.add (Int64.repr (cursor - 1)) (Int64.repr 1) = Int64.repr cursor.
Proof.
  unfold Int64.add. change Int64.one with (Int64.repr 1).
  rewrite !cursor_unsigned by lia. f_equal; lia.
Qed.
Lemma bitpos_shift_bound : Int64.ltu (Int64.repr (cursor - 1)) Int64.iwordsize = true.
Proof.
  unfold Int64.ltu. change Int64.iwordsize with (Int64.repr 64).
  rewrite !cursor_unsigned by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Ltac bitpos_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu
    Int64.modu Int64.ltu Int64.shl Int64.or];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu
    Int64.modu Int64.ltu Int64.shl Int64.or];
  change (Int.signed (Int.repr 1)) with 1;
  repeat first [
    rewrite cursor_sub by lia
  | rewrite bitpos_index
  | rewrite bitpos_remainder
  | rewrite bitpos_width
  | rewrite bitpos_shift_bound ];
  reflexivity.

Ltac eval_bitpos :=
  first [ solve [apply eval_generated_uword_bits]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [eval_bitpos | bitpos_scalar])
        | (eapply eval_Eunop; [eval_bitpos | bitpos_scalar])
        | (eapply eval_Ebinop; [eval_bitpos | eval_bitpos | bitpos_scalar])
        | apply eval_Econst_int
        | apply eval_Econst_long ].

Definition le_bitpos_offset (bf : block) : temp_env :=
  PTree.set _t'8 (Vlong (Int64.repr cursor)) (le_writeBit0 bf).

Definition le_bitpos_edge (bf bw : block) : temp_env :=
  PTree.set _t'6 (Vptr bw Ptrofs.zero) (le_bitpos_offset bf).

Definition le_bitpos_t7 (bf bw : block) : temp_env :=
  PTree.set _t'7 (Vlong (Int64.repr (cursor - 1))) (le_bitpos_edge bf bw).

Definition le_bitpos_ptr (bf bw : block) : temp_env :=
  PTree.set _dst_ptr (Vptr bw Ptrofs.zero) (le_bitpos_t7 bf bw).

Definition le_bitpos_t2 (w : int64) (bf bw : block) : temp_env :=
  PTree.set _t'2 (Vlong w) (le_bitpos_ptr bf bw).

Definition le_bitpos_t3 (w : int64) (bf bw : block) : temp_env :=
  PTree.set _t'3 (Vlong (Int64.repr (cursor - 1))) (le_bitpos_t2 w bf bw).

Definition le_bitpos_t1 (w c : int64) (bf bw : block) : temp_env :=
  PTree.set _t'1 (Vlong c) (le_bitpos_t3 w bf bw).

Section ClearBitWord.
Variable w c : int64.

Lemma eval_writeBit_zero_position_body : forall (m m1 m2 : mem) (bf bw : block),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor - 1))) = Some m1 ->
  Mem.load Mptr m1 bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr (cursor - 1))) ->
  Mem.load Mint64 m1 bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m1 bw 0 (Vlong c) = Some m2 ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some block_LSBclear ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_LSBclear Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  ClightBigstep.Clight2.eval_funcall ge0 m1 (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr cursor) :: nil) E0 m1
    (Vlong c) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_writeBit0 bf) m
    (fn_body f_writeBit) E0 (le_bitpos_t1 w c bf bw) m2
    (Out_return (Some (Vint Int.zero, tbool))).
Proof.
  intros m m1 m2 bf bw Hedge Hoffset Hstore_offset Hedge1 Hoffset1
    Hword Hstore_word Hsym Hfun Hclear.
  unfold f_writeBit; cbn [fn_body].
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_writeBit_debug_loop.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set.
        eapply eval_frame_offset.
        { cbn [le_writeBit0]; reflexivity. }
        { exact Hoffset. }
      * eapply exec_Sassign_value.
        -- apply eval_frame_offset_lvalue.
           cbn [le_bitpos_offset le_writeBit0]; reflexivity.
        -- eapply eval_Ebinop.
           ++ eapply eval_Etempvar.
              cbn [le_bitpos_offset le_writeBit0]; reflexivity.
           ++ apply eval_Econst_int.
           ++ bitpos_scalar.
        -- bitpos_scalar.
        -- apply assign_frame_offset with
             (le := le_bitpos_offset bf).
           ++ cbn [le_bitpos_offset le_writeBit0]; reflexivity.
           ++ exact Hstore_offset.
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
           eapply eval_frame_edge.
           ++ cbn [le_bitpos_offset le_writeBit0]; reflexivity.
           ++ exact Hedge1.
        -- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_set.
              eapply eval_frame_offset.
              { cbn [le_bitpos_edge le_bitpos_offset le_writeBit0].
                reflexivity. }
              { exact Hoffset1. }
           ++ apply exec_set.
              eapply eval_Ebinop.
              ** eapply eval_Etempvar.
                 cbn [le_bitpos_edge le_bitpos_offset le_writeBit0].
                 reflexivity.
              ** eapply eval_Ebinop.
                 --- eapply eval_Etempvar.
                     cbn [le_bitpos_t7 le_bitpos_edge
                       le_bitpos_offset le_writeBit0]. reflexivity.
                 --- eval_bitpos.
                 --- bitpos_scalar.
              ** bitpos_scalar.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply ClightBigstep.exec_Sifthenelse
             with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Etempvar.
              cbn [le_writeBit0]; reflexivity.
           ++ reflexivity.
           ++ eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- apply exec_set.
                     eapply eval_dst_word.
                     +++ cbn [le_bitpos_ptr le_bitpos_t7
                           le_bitpos_edge le_bitpos_offset le_writeBit0].
                         reflexivity.
                     +++ exact Hword.
                 --- eapply ClightBigstep.exec_Sseq_1
                       with (t1 := E0) (t2 := E0).
                     +++ apply exec_set.
                         eapply eval_frame_offset.
                         { cbn [le_bitpos_t2 le_bitpos_ptr
                             le_bitpos_t7 le_bitpos_edge
                             le_bitpos_offset le_writeBit0]. reflexivity. }
                         { exact Hoffset1. }
                     +++ eapply ClightBigstep.exec_Scall
                           with (vf := Vptr block_LSBclear Ptrofs.zero)
                                (vargs := Vlong w ::
                                  Vlong (Int64.repr cursor) :: nil)
                                (f := Internal f_LSBclear)
                                (vres := Vlong c).
                         ---- vm_compute; reflexivity.
                         ---- eapply eval_Elvalue.
                              { eapply eval_Evar_global.
                                - simpl; reflexivity.
                                - exact Hsym. }
                              { apply deref_loc_reference.
                                change (access_mode
                                  (Tfunction
                                    (Tcons tulong (Tcons tulong Tnil))
                                    tulong cc_default) = By_reference).
                                reflexivity. }
                         ---- eapply eval_Econs.
                              { eapply eval_Etempvar.
                                cbn [le_bitpos_t2 le_bitpos_ptr
                                  le_bitpos_t7 le_bitpos_edge
                                  le_bitpos_offset le_writeBit0].
                                reflexivity. }
                              { reflexivity. }
                              { eapply eval_Econs.
                                - eval_bitpos.
                                - bitpos_scalar.
                                - apply eval_Enil. }
                         ---- exact Hfun.
                         ---- vm_compute; reflexivity.
                         ---- exact Hclear.
              ** eapply exec_Sassign_value.
                   { apply eval_dst_word_lvalue.
                     cbn [le_bitpos_ptr le_bitpos_t7 le_bitpos_edge
                       le_bitpos_offset le_writeBit0]. reflexivity. }
                   { eapply eval_Etempvar.
                     cbn [le_bitpos_t1 le_bitpos_t3 le_bitpos_t2
                       le_bitpos_ptr le_bitpos_t7 le_bitpos_edge
                       le_bitpos_offset le_writeBit0]. reflexivity. }
                   { bitpos_scalar. }
                   { apply assign_dst_word with
                       (le := le_bitpos_t1 w c bf bw).
                     - cbn [le_bitpos_t1 le_bitpos_t3 le_bitpos_t2
                         le_bitpos_ptr le_bitpos_t7 le_bitpos_edge
                         le_bitpos_offset le_writeBit0]. reflexivity.
                     - exact Hstore_word. }
    -- apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Etempvar.
    cbn [le_bitpos_t1 le_bitpos_t3 le_bitpos_t2 le_bitpos_ptr
      le_bitpos_t7 le_bitpos_edge le_bitpos_offset le_writeBit0].
    reflexivity.
Qed.

End ClearBitWord.

Definition le_bit1pos_offset (bf : block) : temp_env :=
  PTree.set _t'8 (Vlong (Int64.repr cursor)) (le_writeBit1 bf).

Definition le_bit1pos_edge (bf bw : block) : temp_env :=
  PTree.set _t'6 (Vptr bw Ptrofs.zero) (le_bit1pos_offset bf).

Definition le_bit1pos_t7 (bf bw : block) : temp_env :=
  PTree.set _t'7 (Vlong (Int64.repr (cursor - 1))) (le_bit1pos_edge bf bw).

Definition le_bit1pos_ptr (bf bw : block) : temp_env :=
  PTree.set _dst_ptr (Vptr bw Ptrofs.zero) (le_bit1pos_t7 bf bw).

Section SetBitWord.
Variable w : int64.

Definition le_bit1pos_t4 (bf bw : block) : temp_env :=
  PTree.set _t'4 (Vlong w) (le_bit1pos_ptr bf bw).

Definition le_bit1pos_t5 (bf bw : block) : temp_env :=
  PTree.set _t'5 (Vlong (Int64.repr (cursor - 1))) (le_bit1pos_t4 bf bw).

Lemma eval_writeBit_one_position_body : forall (m m1 m2 : mem) (bf bw : block),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor - 1))) = Some m1 ->
  Mem.load Mptr m1 bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr (cursor - 1))) ->
  Mem.load Mint64 m1 bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m1 bw 0 (Vlong (Int64.or w (Int64.shl Int64.one (Int64.repr (cursor - 1))))) = Some m2 ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_writeBit1 bf) m
    (fn_body f_writeBit) E0 (le_bit1pos_t5 bf bw) m2
    (Out_return (Some (Vint Int.one, tbool))).
Proof.
  intros m m1 m2 bf bw Hedge Hoffset Hstore_offset Hedge1 Hoffset1
    Hword Hstore_word.
  unfold f_writeBit; cbn [fn_body].
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_writeBit_debug_loop.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set.
        eapply eval_frame_offset.
        { cbn [le_writeBit1]; reflexivity. }
        { exact Hoffset. }
      * eapply exec_Sassign_value.
        -- apply eval_frame_offset_lvalue.
           cbn [le_bit1pos_offset le_writeBit1]; reflexivity.
        -- eapply eval_Ebinop.
           ++ eapply eval_Etempvar.
              cbn [le_bit1pos_offset le_writeBit1]; reflexivity.
           ++ apply eval_Econst_int.
           ++ bitpos_scalar.
        -- bitpos_scalar.
        -- apply assign_frame_offset with (le := le_bit1pos_offset bf).
           ++ cbn [le_bit1pos_offset le_writeBit1]; reflexivity.
           ++ exact Hstore_offset.
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
           eapply eval_frame_edge.
           ++ cbn [le_bit1pos_offset le_writeBit1]; reflexivity.
           ++ exact Hedge1.
        -- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_set.
              eapply eval_frame_offset.
              { cbn [le_bit1pos_edge le_bit1pos_offset le_writeBit1].
                reflexivity. }
              { exact Hoffset1. }
           ++ apply exec_set.
              eapply eval_Ebinop.
              ** eapply eval_Etempvar.
                 cbn [le_bit1pos_edge le_bit1pos_offset le_writeBit1].
                 reflexivity.
              ** eapply eval_Ebinop.
                 --- eapply eval_Etempvar.
                     cbn [le_bit1pos_t7 le_bit1pos_edge
                       le_bit1pos_offset le_writeBit1]. reflexivity.
                 --- eval_bitpos.
                 --- bitpos_scalar.
              ** bitpos_scalar.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply ClightBigstep.exec_Sifthenelse
             with (v1 := Vint Int.one) (b := true).
           ++ eapply eval_Etempvar.
              cbn [le_writeBit1]; reflexivity.
           ++ reflexivity.
           ++ eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_set.
                 eapply eval_dst_word.
                 { cbn [le_bit1pos_ptr le_bit1pos_t7
                     le_bit1pos_edge le_bit1pos_offset le_writeBit1].
                   reflexivity. }
                 { exact Hword. }
              ** eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- apply exec_set.
                     eapply eval_frame_offset.
                     { cbn [le_bit1pos_t4 le_bit1pos_ptr
                         le_bit1pos_t7 le_bit1pos_edge
                         le_bit1pos_offset le_writeBit1]. reflexivity. }
                     { exact Hoffset1. }
                 --- eapply exec_Sassign_value.
                     { apply eval_dst_word_lvalue.
                       cbn [le_bit1pos_ptr le_bit1pos_t7
                         le_bit1pos_edge le_bit1pos_offset le_writeBit1].
                       reflexivity. }
                     { eapply eval_Ebinop.
                       - eapply eval_Etempvar.
                         cbn [le_bit1pos_t4 le_bit1pos_ptr
                           le_bit1pos_t7 le_bit1pos_edge
                           le_bit1pos_offset le_writeBit1]. reflexivity.
                       - eapply eval_Ecast.
                         + eapply eval_Ebinop.
                           * eapply eval_Ecast.
                             { apply eval_Econst_int. }
                             { bitpos_scalar. }
                           * eapply eval_Ebinop.
                             { eapply eval_Etempvar.
                               cbn [le_bit1pos_t5 le_bit1pos_t4
                                 le_bit1pos_ptr le_bit1pos_t7
                                 le_bit1pos_edge le_bit1pos_offset
                                 le_writeBit1]. reflexivity. }
                             { eval_bitpos. }
                             { bitpos_scalar. }
                           * bitpos_scalar.
                         + bitpos_scalar.
                       - bitpos_scalar. }
                     { bitpos_scalar. }
                     { apply assign_dst_word with
                         (le := le_bit1pos_t5 bf bw).
                       - cbn [le_bit1pos_t5 le_bit1pos_t4
                           le_bit1pos_ptr le_bit1pos_t7 le_bit1pos_edge
                           le_bit1pos_offset le_writeBit1]. reflexivity.
                       - exact Hstore_word. }
    -- apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Etempvar.
    cbn [le_bit1pos_t5 le_bit1pos_t4 le_bit1pos_ptr le_bit1pos_t7
      le_bit1pos_edge le_bit1pos_offset le_writeBit1]. reflexivity.
Qed.

End SetBitWord.

Lemma eval_writeBit_false_position m m1 m2 bf bw w :
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor - 1))) = Some m1 ->
  Mem.store Mint64 m1 bw 0 (Vlong (clear_low cursor w)) = Some m2 ->
  bf <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bf Ptrofs.zero; Vint Int.zero] E0 m2 (Vint Int.zero).
Proof.
  intros HE HO HW SO SW Hneq.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_writeBit0 bf) (m1 := m)
      (le2 := le_bitpos_t1 w (clear_low cursor w) bf bw) (m2 := m2)
      (out := Out_return (Some (Vint Int.zero, tbool))) (vres := Vint Int.zero).
  - apply entry_writeBit0.
  - eapply eval_writeBit_zero_position_body.
    + exact HE.
    + exact HO.
    + exact SO.
    + rewrite <- HE. eapply Mem.load_store_other;
        [exact SO | right; left; change (0 + 8 <= 8); lia].
    + exact (Mem.load_store_same _ _ _ _ _ _ SO).
    + rewrite <- HW. eapply Mem.load_store_other; [exact SO | auto].
    + exact SW.
    + apply symbol_LSBclear.
    + apply funct_LSBclear.
    + apply eval_clear_width; exact Hcursor.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Lemma eval_writeBit_true_position m m1 m2 bf bw w :
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor - 1))) = Some m1 ->
  Mem.store Mint64 m1 bw 0 (Vlong (Int64.or w (Int64.shl Int64.one (Int64.repr (cursor - 1))))) = Some m2 ->
  bf <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bf Ptrofs.zero; Vint Int.one] E0 m2 (Vint Int.one).
Proof.
  intros HE HO HW SO SW Hneq.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_writeBit1 bf) (m1 := m)
      (le2 := le_bit1pos_t5 w bf bw) (m2 := m2)
      (out := Out_return (Some (Vint Int.one, tbool))) (vres := Vint Int.one).
  - apply entry_writeBit1.
  - eapply eval_writeBit_one_position_body.
    + exact HE.
    + exact HO.
    + exact SO.
    + rewrite <- HE. eapply Mem.load_store_other;
        [exact SO | right; left; change (0 + 8 <= 8); lia].
    + exact (Mem.load_store_same _ _ _ _ _ _ SO).
    + rewrite <- HW. eapply Mem.load_store_other; [exact SO | auto].
    + exact SW.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

End Position.

(** Actual carry-bit writes into the second backing word, at cursors 65..128. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_word_bits C.jet_frame_arith C.jet_frame_constants.
Require Import C.jet_frame_access C.jet_LSBclear_width C.jet_writeBit C.jet_writeBit_position.
Require Import C.jet_write8_crossing.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Lemma high_bit_index k : 1 <= k <= 64 ->
  Int64.divu (Int64.repr (64 + k - 1)) (Int64.repr 64) = Int64.one.
Proof.
  intros HK. unfold Int64.divu. rewrite !cursor_unsigned by lia.
  replace ((64 + k - 1) / 64) with 1; [reflexivity |].
  apply Z.div_unique with (r := k - 1); lia.
Qed.

Lemma high_bit_remainder k : 1 <= k <= 64 ->
  Int64.modu (Int64.repr (64 + k - 1)) (Int64.repr 64) = Int64.repr (k - 1).
Proof.
  intros HK. unfold Int64.modu. rewrite !cursor_unsigned by lia.
  f_equal. symmetry. apply Z.mod_unique with (q := 1); lia.
Qed.

Ltac high_bit_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge; [reflexivity | eassumption]]
        | solve [eapply eval_frame_offset; [reflexivity | eassumption]]
        | solve [eapply eval_Elvalue;
            [eapply eval_Ederef; eapply eval_Etempvar; reflexivity
            | eapply deref_loc_value; [reflexivity | eassumption]]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [high_bit_expr | crossing_scalar])
        | (eapply eval_Eunop; [high_bit_expr | crossing_scalar])
        | (eapply eval_Ebinop; [high_bit_expr | high_bit_expr | crossing_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac high_bit_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [high_bit_stmt | high_bit_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      apply exec_writeBit_debug_loop
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; high_bit_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      first [
        eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
          [high_bit_expr | reflexivity | high_bit_stmt]
      | eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
          [high_bit_expr | reflexivity | high_bit_stmt] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBclear _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBclear);
      [reflexivity | reflexivity | reflexivity | apply symbol_LSBclear | apply funct_LSBclear
      | high_bit_expr | high_bit_expr | apply eval_clear_width; lia]
  | |- ClightBigstep.exec_stmt _ _ _ ?temps _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [apply eval_frame_offset_lvalue; reflexivity | high_bit_expr | crossing_scalar
      | eapply assign_frame_offset with (le := temps); [reflexivity | eassumption]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Ederef _ _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [eapply eval_Ederef; eapply eval_Etempvar; reflexivity
      | high_bit_expr | crossing_scalar | apply assign_frame_word_at; eassumption]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; high_bit_expr
  end.

Lemma eval_writeBit_false_high m mo mf bd bw old k :
  1 <= k <= 64 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong old) ->
  Mem.store Mint64 m bd 8 (Vlong (Int64.repr (64 + k - 1))) = Some mo ->
  Mem.store Mint64 mo bw 8 (Vlong (clear_low k old)) = Some mf ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd Ptrofs.zero; Vint Int.zero] E0 mf (Vint Int.zero).
Proof.
  intros HK HE HO HW SO SW HD.
  assert (HEo : Mem.load Mptr mo bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_store_other; [exact HE | exact SO | right; left; cbn; lia]. }
  pose proof (Mem.load_store_same _ _ _ _ _ _ SO) as HOo.
  assert (HWo : Mem.load Mint64 mo bw 8 = Some (Vlong old)).
  { erewrite Mem.load_store_other; [exact HW | exact SO | auto]. }
  pose proof (cursor_sub (64 + k) 1 ltac:(lia) ltac:(lia)) as Hsub.
  pose proof (high_bit_index k HK) as Hindex.
  pose proof (high_bit_remainder k HK) as Hrem.
  pose proof (bitpos_width k HK) as Hwidth.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_writeBit0 bd) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint Int.zero, tbool))) (vres := Vint Int.zero).
  - apply entry_writeBit0.
  - unfold f_writeBit; cbn [fn_body]. timeout 10 high_bit_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Lemma eval_writeBit_true_high m mo mf bd bw old k :
  1 <= k <= 64 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong old) ->
  Mem.store Mint64 m bd 8 (Vlong (Int64.repr (64 + k - 1))) = Some mo ->
  Mem.store Mint64 mo bw 8
    (Vlong (Int64.or old (Int64.shl Int64.one (Int64.repr (k - 1))))) = Some mf ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd Ptrofs.zero; Vint Int.one] E0 mf (Vint Int.one).
Proof.
  intros HK HE HO HW SO SW HD.
  assert (HEo : Mem.load Mptr mo bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_store_other; [exact HE | exact SO | right; left; cbn; lia]. }
  pose proof (Mem.load_store_same _ _ _ _ _ _ SO) as HOo.
  assert (HWo : Mem.load Mint64 mo bw 8 = Some (Vlong old)).
  { erewrite Mem.load_store_other; [exact HW | exact SO | auto]. }
  pose proof (cursor_sub (64 + k) 1 ltac:(lia) ltac:(lia)) as Hsub.
  pose proof (high_bit_index k HK) as Hindex.
  pose proof (high_bit_remainder k HK) as Hrem.
  pose proof (bitpos_shift_bound k HK) as Hshift.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_writeBit1 bd) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint Int.one, tbool))) (vres := Vint Int.one).
  - apply entry_writeBit1.
  - unfold f_writeBit; cbn [fn_body]. timeout 10 high_bit_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

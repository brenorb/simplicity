(** Generated read8 for every non-crossing input cursor within a word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_read8 C.jet_write8 C.jets
  C.jet_frame_arith C.jet_frame_constants C.jet_frame_access.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition read8_at cursor w := read8_result (Int64.shru w (Int64.repr (56 - cursor))).

Lemma read8_cursor_arithmetic cursor : 0 <= cursor <= 56 ->
  Int64.divu (Int64.repr cursor) (Int64.repr 64) = Int64.zero /\
  Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr cursor /\
  Int64.sub (Int64.repr 64) (Int64.repr cursor) = Int64.repr (64 - cursor) /\
  Int64.ltu (Int64.repr (64 - cursor)) (Int64.repr 8) = false /\
  Int64.sub (Int64.repr (64 - cursor)) (Int64.repr 8) = Int64.repr (56 - cursor) /\
  Int64.ltu (Int64.repr (56 - cursor)) Int64.iwordsize = true /\
  Int64.add (Int64.repr cursor) (Int64.repr 8) = Int64.repr (cursor + 8).
Proof.
  intros HC. repeat split.
  - unfold Int64.divu. rewrite !cursor_unsigned by lia.
    rewrite Z.div_small by lia. reflexivity.
  - unfold Int64.modu. rewrite !cursor_unsigned by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - apply cursor_sub; lia.
  - unfold Int64.ltu. rewrite !cursor_unsigned by lia.
    rewrite zlt_false by lia. reflexivity.
  - rewrite cursor_sub by lia. f_equal; lia.
  - unfold Int64.ltu. change Int64.iwordsize with (Int64.repr 64).
    rewrite !cursor_unsigned by lia. rewrite zlt_true by lia. reflexivity.
  - unfold Int64.add. rewrite !cursor_unsigned by lia. reflexivity.
Qed.

Ltac readpos_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int.repr Int.zero_ext Int.or Z.sub Z.add];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int.repr Int.zero_ext Int.or Z.sub Z.add];
  change (Int.signed (Int.repr 8)) with 8;
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity | eassumption].

Ltac readpos_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_ofs; [reflexivity | eassumption]]
        | solve [eapply eval_frame_offset; [reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at; [reflexivity | eassumption]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [readpos_expr | readpos_scalar])
        | (eapply eval_Eunop; [readpos_expr | readpos_scalar])
        | (eapply eval_Ebinop; [readpos_expr | readpos_expr | readpos_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac readpos_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [readpos_stmt | readpos_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; readpos_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [readpos_expr | reflexivity | apply exec_Sskip]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | readpos_expr | readpos_expr | apply eval_LSBkeep8_value ]
  | |- ClightBigstep.exec_stmt _ _ _ ?currenttemps _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue; reflexivity | readpos_expr | readpos_scalar
      | eapply assign_frame_offset with (le := currenttemps); [reflexivity | readpos_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; readpos_expr
  end.

Lemma eval_read8_position m mf bf bw w cursor :
  0 <= cursor <= 56 ->
  Mem.load Mptr m bf 0 = Some (Vptr bw (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor + 8))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf Ptrofs.zero] E0 mf (Vint (read8_at cursor w)).
Proof.
  intros HC HE HO HW SF.
  pose proof (read8_cursor_arithmetic cursor HC) as HA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8 bf) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read8_at cursor w), tuchar)))
      (vres := Vint (read8_at cursor w)).
  - apply entry_read8.
  - unfold f_simplicity_read8; cbn [fn_body].
    timeout 10 readpos_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_at cursor w))) = Some (Vint (read8_at cursor w))).
    unfold read8_at, read8_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

(** Actual write8 crossing branch for the byte used by one_8.
    The high word is at offset 8, the next word at offset 0. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_write8 C.jets C.jet_frame_arith C.jet_frame_constants
  C.jet_frame_access C.jet_LSBclear_width C.jet_LSBkeep_width C.jet_word_bits C.jet_crossing_arith.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Ltac crossing_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shl Int64.shru Int64.or Int64.loword Int.shr Int.repr Z.sub Z.add];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shl Int64.shru Int64.or Int64.loword Int.shr Int.repr Z.sub Z.add];
  change (Int.signed (Int.repr 1)) with 1;
  change (Int.signed (Int.repr 8)) with 8;
  change (Int64.repr (Int.signed Int.zero)) with Int64.zero;
  change (Int64.repr (Int.unsigned Int.one)) with Int64.one;
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  try rewrite clear_entire_word;
  try rewrite Int64.or_zero;
  try rewrite Int64.or_zero_l;
  first [reflexivity | eassumption].

Ltac crossing_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge; [reflexivity | eassumption]]
        | solve [eapply eval_frame_offset; [reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at; [reflexivity | eassumption]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [crossing_expr | crossing_scalar])
        | (eapply eval_Eunop; [crossing_expr | crossing_scalar])
        | (eapply eval_Ebinop; [crossing_expr | crossing_expr | crossing_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac crossing_call funbody sym funproof :=
  eapply call_word_helper with (f := funbody);
  [ reflexivity | reflexivity | reflexivity | apply sym | apply funproof
  | crossing_expr | crossing_expr
  | first [ apply eval_clear_width; lia | apply eval_keep_width; lia ] ].

Ltac crossing_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [crossing_stmt | crossing_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; crossing_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [crossing_expr | reflexivity | crossing_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      eapply exec_Sloop_stop1 with (out' := Out_break);
      [ eapply exec_Sseq_2;
        [ eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
          [crossing_expr | reflexivity | apply exec_Sbreak]
        | discriminate ]
      | constructor ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      unfold Swhile; crossing_stmt
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBclear _) _) _ _ _ _ =>
      crossing_call f_LSBclear symbol_LSBclear funct_LSBclear
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      crossing_call f_LSBkeep symbol_LSBkeep funct_LSBkeep
  | |- ClightBigstep.exec_stmt _ _ _ ?currenttemps _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue; reflexivity
      | crossing_expr | crossing_scalar
      | eapply assign_frame_offset with (le := currenttemps);
        [reflexivity | first [eassumption | crossing_scalar]] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Ederef _ _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_word_lvalue_at; reflexivity
      | crossing_expr | crossing_scalar
      | apply assign_frame_word_at; first [eassumption | crossing_scalar] ]
  end.

Lemma eval_write8_crossing_one_raw m mh mo ml mf bd bw k oldhigh oldlow :
  1 <= k <= 7 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong oldhigh) ->
  Mem.store Mint64 m bw 8 (Vlong (clear_low k oldhigh)) = Some mh ->
  Mem.load Mint64 mh bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.store Mint64 mh bd 8 (Vlong (Int64.repr 64)) = Some mo ->
  Mem.load Mint64 mo bw 0 = Some (Vlong oldlow) ->
  Mem.store Mint64 mo bw 0 (Vlong (Int64.shl Int64.one (Int64.repr (56 + k)))) = Some ml ->
  Mem.load Mint64 ml bd 8 = Some (Vlong (Int64.repr 64)) ->
  Mem.store Mint64 ml bd 8 (Vlong (Int64.repr (56 + k))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd Ptrofs.zero; Vint Int.one] E0 mf Vundef.
Proof.
  intros HK HE HO HH SH HOh SO HL SL HOl SF.
  pose proof (byte_crossing_arithmetic_holds k HK) as HA.
  unfold byte_crossing_arithmetic in HA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_write8_x bd Int.one) (m1 := m)
      (m2 := mf) (out := Out_normal) (vres := Vundef).
  - apply entry_write8_x.
  - unfold f_simplicity_write8; cbn [fn_body].
    timeout 10 crossing_stmt.
  - reflexivity.
  - reflexivity.
Qed.

(** Initial loads suffice: all intervening reads follow from the four stores. *)
Lemma eval_write8_crossing_one m mh mo ml mf bd bw k oldhigh oldlow :
  1 <= k <= 7 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong oldhigh) ->
  Mem.load Mint64 m bw 0 = Some (Vlong oldlow) ->
  Mem.store Mint64 m bw 8 (Vlong (clear_low k oldhigh)) = Some mh ->
  Mem.store Mint64 mh bd 8 (Vlong (Int64.repr 64)) = Some mo ->
  Mem.store Mint64 mo bw 0 (Vlong (Int64.shl Int64.one (Int64.repr (56 + k)))) = Some ml ->
  Mem.store Mint64 ml bd 8 (Vlong (Int64.repr (56 + k))) = Some mf ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd Ptrofs.zero; Vint Int.one] E0 mf Vundef.
Proof.
  intros HK HE HO HH HL SH SO SL SF Hneq.
  eapply eval_write8_crossing_one_raw; eauto.
  - rewrite <- HO. eapply Mem.load_store_other; [exact SH | auto].
  - erewrite Mem.load_store_other; [|exact SO|auto].
    erewrite Mem.load_store_other; [exact HL|exact SH|right; left; cbn; lia].
  - erewrite Mem.load_store_other; [|exact SL|auto].
    exact (Mem.load_store_same _ _ _ _ _ _ SO).
Qed.

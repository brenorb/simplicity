(** Generated read8 across the first two backing words.
    The edge is at offset 16; reading starts in word 8 and ends in word 0. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_read8 C.jet_write8 C.jets C.jet_frame_arith.
Require Import C.jet_frame_constants C.jet_frame_access C.jet_LSBkeep_width.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition read8_narrow w := Int.zero_ext 8 (Int.repr (Int64.unsigned w)).
Definition read8_crossing_high k high :=
  Int.zero_ext 8 (Int.or Int.zero
    (Int.zero_ext 8 (Int.shl (read8_narrow (Int64.zero_ext k high))
      (Int64.loword (Int64.repr (8 - k)))))).
Definition read8_crossing_result k high low :=
  Int.zero_ext 8 (Int.or (read8_crossing_high k high)
    (read8_narrow (Int64.zero_ext (8 - k) (Int64.shru low (Int64.repr (56 + k)))))).

Lemma read8_crossing_arithmetic k : 1 <= k <= 7 ->
  Int64.divu (Int64.repr (64 - k)) (Int64.repr 64) = Int64.zero /\
  Int64.modu (Int64.repr (64 - k)) (Int64.repr 64) = Int64.repr (64 - k) /\
  Int64.sub (Int64.repr 64) (Int64.repr (64 - k)) = Int64.repr k /\
  Int64.ltu (Int64.repr k) (Int64.repr 8) = true /\
  Int64.sub (Int64.repr 8) (Int64.repr k) = Int64.repr (8 - k) /\
  Int64.ltu (Int64.repr (8 - k)) (Int64.repr 32) = true /\
  Int64.add (Int64.repr (64 - k)) (Int64.repr k) = Int64.repr 64 /\
  Int64.ltu (Int64.repr 64) (Int64.repr (8 - k)) = false /\
  Int64.sub (Int64.repr 64) (Int64.repr (8 - k)) = Int64.repr (56 + k) /\
  Int64.ltu (Int64.repr (56 + k)) Int64.iwordsize = true /\
  Int64.add (Int64.repr 64) (Int64.repr (8 - k)) = Int64.repr (72 - k).
Proof.
  intros HK.
  assert (HC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    repeat split; reflexivity.
Qed.

Ltac readcross_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.zero_ext Int64.loword Int.repr Int.zero_ext Int.or Int.shl Z.sub Z.add];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.zero_ext Int64.loword Int.repr Int.zero_ext Int.or Int.shl Z.sub Z.add];
  change (Int.signed (Int.repr 8)) with 8;
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity | eassumption].

Ltac readcross_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_ofs; [reflexivity | eassumption]]
        | solve [eapply eval_frame_offset; [reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at; [reflexivity | eassumption]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [readcross_expr | readcross_scalar])
        | (eapply eval_Eunop; [readcross_expr | readcross_scalar])
        | (eapply eval_Ebinop; [readcross_expr | readcross_expr | readcross_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac readcross_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [readcross_stmt | readcross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; readcross_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [readcross_expr | reflexivity | readcross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      unfold Swhile; readcross_stmt
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      eapply exec_Sloop_stop1 with (out' := Out_break);
      [ eapply exec_Sseq_2;
        [ eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
          [readcross_expr | reflexivity | apply exec_Sbreak]
        | discriminate ]
      | constructor ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | readcross_expr | readcross_expr | apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ ?temps _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue; reflexivity | readcross_expr | readcross_scalar
      | eapply assign_frame_offset with (le := temps); [reflexivity | readcross_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; readcross_expr
  end.

Lemma eval_read8_crossing_raw m mm mf bf bw k high low :
  1 <= k <= 7 ->
  Mem.load Mptr m bf 0 = Some (Vptr bw (Ptrofs.repr 16)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr (64 - k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong high) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 64)) = Some mm ->
  Mem.load Mint64 mm bw 0 = Some (Vlong low) ->
  Mem.load Mint64 mm bf 8 = Some (Vlong (Int64.repr 64)) ->
  Mem.store Mint64 mm bf 8 (Vlong (Int64.repr (72 - k))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf Ptrofs.zero] E0 mf (Vint (read8_crossing_result k high low)).
Proof.
  intros HK HE HO HH SM HL HOm SF.
  pose proof (read8_crossing_arithmetic k HK) as HA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8 bf) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read8_crossing_result k high low), tuchar)))
      (vres := Vint (read8_crossing_result k high low)).
  - apply entry_read8.
  - unfold f_simplicity_read8; cbn [fn_body]. timeout 10 readcross_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_crossing_result k high low))) =
      Some (Vint (read8_crossing_result k high low))).
    unfold read8_crossing_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

Lemma eval_read8_crossing m mm mf bf bw k high low :
  1 <= k <= 7 ->
  Mem.load Mptr m bf 0 = Some (Vptr bw (Ptrofs.repr 16)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr (64 - k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong high) ->
  Mem.load Mint64 m bw 0 = Some (Vlong low) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 64)) = Some mm ->
  Mem.store Mint64 mm bf 8 (Vlong (Int64.repr (72 - k))) = Some mf ->
  bf <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf Ptrofs.zero] E0 mf (Vint (read8_crossing_result k high low)).
Proof.
  intros HK HE HO HH HL SM SF HD.
  eapply eval_read8_crossing_raw; eauto.
  - erewrite Mem.load_store_other; [exact HL|exact SM|auto].
  - exact (Mem.load_store_same _ _ _ _ _ _ SM).
Qed.

(** Generated Clight execution for aligned read64 cursors. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access.
Require Import C.jet_frame_constants C.jet_frame_arith C.jet_LSBkeep_width.
Require Import C.jet_read8_layout C.jet_read16_layout_exec C.jet_read32_layout_exec.
Require Import C.jet_read64_input_word.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition le_read64_layout (bf : block) (base : Z) : temp_env :=
  PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps f_simplicity_read64.(fn_temps)).

Lemma entry_read64_layout m bf base :
  function_entry2 ge0 f_simplicity_read64 [Vptr bf (Ptrofs.repr base)]
    m empty_env (le_read64_layout bf base) m.
Proof.
  constructor.
  - constructor.
  - constructor; [simpl; tauto | constructor].
  - intros id1 id2 H1 H2 Heq. simpl in H1, H2. subst id2.
    repeat match goal with H : _ \/ _ |- _ => destruct H end.
    all: vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_read64_final_shift le m shift n k high :
  le!_t'4 = Some (Vlong high) ->
  le!_frame_shift = Some (Vlong (Int64.repr shift)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Int64.sub (Int64.repr shift) (Int64.repr n) = Int64.repr k ->
  Int64.ltu (Int64.repr k) Int64.iwordsize = true ->
  eval_expr ge0 empty_env le m
    (Ecast
      (Ebinop Oshr (Etempvar _t'4 tulong)
        (Ebinop Osub (Etempvar _frame_shift tulong)
          (Etempvar _n tulong) tulong) tulong) tulong)
    (Vlong (Int64.shru high (Int64.repr k))).
Proof.
  intros HT Hshift Hn Hsub Hvalid.
  eapply eval_Ecast with (v1 := Vlong (Int64.shru high (Int64.repr k))).
  - eapply eval_Ebinop with (v1 := Vlong high) (v2 := Vlong (Int64.repr k)).
    + eapply eval_Etempvar. exact HT.
    + eapply eval_Ebinop with
        (v1 := Vlong (Int64.repr shift)) (v2 := Vlong (Int64.repr n)).
      * eapply eval_Etempvar. exact Hshift.
      * eapply eval_Etempvar. exact Hn.
      * change (Some (Vlong (Int64.sub (Int64.repr shift) (Int64.repr n))) =
          Some (Vlong (Int64.repr k))). rewrite Hsub. reflexivity.
    + change
        ((if Int64.ltu (Int64.repr k) Int64.iwordsize
          then Some (Vlong (Int64.shru high (Int64.repr k))) else None) =
         Some (Vlong (Int64.shru high (Int64.repr k)))).
      rewrite Hvalid. reflexivity.
  - reflexivity.
Qed.

Lemma read64_aligned_result high :
  Int64.or (Int64.repr (Int.signed (Int.repr 0)))
    (Int64.zero_ext 64 (Int64.shru high (Int64.repr 0))) = high.
Proof.
  replace (Int.signed (Int.repr 0)) with 0 by reflexivity.
  replace (Int64.repr 0) with Int64.zero by reflexivity.
  rewrite Int64.or_zero_l.
  rewrite Int64.zero_ext_above by
    (unfold Int64.zwordsize, Int64.wordsize, Wordsize_64.wordsize; lia).
  rewrite Int64.shru_zero. reflexivity.
Qed.

Ltac read64_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.shl Int64.and Int64.or Int.repr Int.zero_ext Int.or
    Z.sub Z.add Int64.zero_ext Int64.loword Int.shl Z.mul Ptrofs.repr Ptrofs.sub
    Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.shl Int64.and Int64.or Int.repr Int.zero_ext Int.or
    Z.sub Z.add Int64.zero_ext Int64.loword Int.shl Z.mul Ptrofs.repr Ptrofs.sub
    Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  replace (Int.signed (Int.repr 64)) with 64 by reflexivity;
  first [reflexivity | eassumption].

Ltac read64_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at;
            [repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
             first [reflexivity | eassumption]
            | repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
              first [reflexivity | eassumption]]]
        | solve [eapply eval_read64_final_shift;
            [reflexivity | reflexivity | reflexivity | eassumption | eassumption]]
        | solve [eapply eval_Etempvar; reflexivity]
        | solve [eapply eval_Etempvar; cbn; rewrite read64_aligned_result; reflexivity]
        | (eapply eval_Etempvar; cbn; try rewrite Int64.or_zero_l; reflexivity)
        | (eapply eval_Ecast; [read64_expr | read32_scalar])
        | (eapply eval_Eunop; [read64_expr | read32_scalar])
        | (eapply eval_Ebinop; [read64_expr | read64_expr | read32_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac read64_cross_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at;
            [repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
             first [reflexivity | eassumption]
            | repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
              first [reflexivity | eassumption]]]
        | solve [eapply eval_read64_final_shift;
            [reflexivity | reflexivity | reflexivity | eassumption | eassumption]]
        | solve [eapply eval_Etempvar; reflexivity]
        | solve [eapply eval_Etempvar; cbn; rewrite read64_aligned_result; reflexivity]
        | (eapply eval_Etempvar; cbn; try rewrite Int64.or_zero_l; reflexivity)
        | (eapply eval_Ecast; [read64_cross_expr | read64_scalar])
        | (eapply eval_Eunop; [read64_cross_expr | read64_scalar])
        | (eapply eval_Ebinop; [read64_cross_expr | read64_cross_expr | read64_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac read64_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [read64_stmt | read64_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read64_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply ClightBigstep.exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [first [eapply eval_read16_unsigned_lt_false;
                  [reflexivity | reflexivity | eassumption]
               | read64_expr]
        | reflexivity | apply ClightBigstep.exec_Sskip]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      eapply exec_read16_while_false; [read64_expr | read32_scalar]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep
      | apply funct_LSBkeep | read64_expr | read64_expr
      | replace (Int.signed (Int.repr 64)) with 64 by reflexivity;
        apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity
      | read64_expr
      | replace (Int.signed (Int.repr 64)) with 64 by reflexivity; read32_scalar
      | replace (Int.signed (Int.repr 64)) with 64 by reflexivity;
        eapply assign_frame_offset_at; [eassumption | read32_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read64_expr
  end.

Ltac read64_cross_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [read64_cross_stmt | read64_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read64_cross_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply ClightBigstep.exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
      [first [eapply eval_read16_unsigned_lt_true;
                [reflexivity | reflexivity | eassumption]
             | read64_cross_expr]
      | reflexivity | read64_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      eapply exec_read16_while_false; [read64_cross_expr | read64_scalar]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [reflexivity | reflexivity | reflexivity
      | apply symbol_LSBkeep | apply funct_LSBkeep
      | read64_cross_expr | read64_cross_expr
      | apply eval_keep_width;
        let G := match goal with |- ?G => constr:(G) end in
        first [match goal with H : G |- _ => exact H end | lia]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [apply eval_frame_offset_lvalue_at; reflexivity
      | read64_cross_expr | read64_scalar
      | eapply assign_frame_offset_at; [eassumption | read64_scalar]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read64_cross_expr
  end.

Theorem eval_read64_layout_aligned m mf bf base bw edge cursor high :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 64 ->
  cursor mod 64 = 0 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + 64))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read64)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong high).
Proof.
  intros HB HC HR HE [HF HO] HH SF.
  assert (Hq : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  pose proof (read8_layout_index cursor ltac:(lia)) as [Hdiv [Hmod _]].
  assert (Hshift : Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr 64) by (rewrite HR; reflexivity).
  assert (Hfinal : Int64.sub (Int64.repr 64) (Int64.repr 64) = Int64.repr 0)
    by reflexivity.
  assert (Hvalid : Int64.ltu Int64.zero Int64.iwordsize = true).
  { change (Int64.ltu (Int64.repr 0) (Int64.repr 64) = true).
    unfold Int64.ltu.
    rewrite !cursor_unsigned by lia. rewrite zlt_true by lia. reflexivity. }
  assert (Hnext : Int64.add (Int64.repr cursor)
      (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr (cursor + 64)).
  { replace (Int.signed (Int.repr 64)) with 64 by reflexivity.
    unfold Int64.add. rewrite !Int64.unsigned_repr by lia. f_equal; lia. }
  pose proof (read8_layout_pointer edge (cursor / 64) Hq HE)
    as [HPfirst HPword].
  assert (Hptr8 : Ptrofs.mul (Ptrofs.repr 8)
      (Ptrofs.of_ints (Int.repr 1)) = Ptrofs.repr 8).
  { unfold Ptrofs.mul, Ptrofs.of_ints. vm_compute. reflexivity. }
  assert (HHp : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) =
      Some (Vlong high)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HH. }
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read64_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vlong high, tulong)))
      (vres := Vlong high).
  - apply entry_read64_layout.
  - unfold f_simplicity_read64; cbn [fn_body].
    timeout 10 read64_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Theorem eval_read64_layout_crossing m mfirst mf bf base bw edge cursor high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 64 ->
  0 < cursor mod 64 < 64 ->
  8 * (2 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  bf <> bw ->
  Mem.store Mint64 m bf (base + 8)
    (Vlong (Int64.repr (cursor + (64 - cursor mod 64)))) = Some mfirst ->
  Mem.store Mint64 mfirst bf (base + 8)
    (Vlong (Int64.repr (cursor + 64))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read64)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong (read64_crossing_at cursor high low)).
Proof.
  intros HB HC HR HE [HF HO] HH HL Hsep SF SFinal.
  assert (Hrem : 0 < cursor mod 64 < 64) by exact HR.
  assert (Hfirst : 0 < 64 - cursor mod 64 < 64) by lia.
  assert (Hwidthfirst : 1 <= 64 - cursor mod 64 <= 64) by lia.
  assert (Hwidthrest : 1 <= cursor mod 64 <= 64) by lia.
  assert (Hshift : Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64)).
  { exact (@cursor_sub 64 (cursor mod 64) ltac:(lia) ltac:(lia)). }
  assert (Hlt : Int64.ltu (Int64.repr (64 - cursor mod 64))
      (Int64.repr 64) = true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia. apply zlt_true. lia. }
  assert (Hleftvalid : Int64.ltu (Int64.repr (cursor mod 64))
      Int64.iwordsize = true).
  { change (Int64.ltu (Int64.repr (cursor mod 64)) (Int64.repr 64) = true).
    unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia. apply zlt_true. lia. }
  assert (Hremain : Int64.sub (Int64.repr 64)
      (Int64.repr (64 - cursor mod 64)) = Int64.repr (cursor mod 64)).
  { pose proof (@cursor_sub 64 (64 - cursor mod 64) ltac:(lia) ltac:(lia)) as H.
    replace (64 - (64 - cursor mod 64)) with (cursor mod 64) in H by lia.
    exact H. }
  assert (Hloop : Int64.ltu (Int64.repr 64)
      (Int64.repr (cursor mod 64)) = false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia. apply zlt_false. lia. }
  assert (Hfinalshift : Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64)).
  { exact Hshift. }
  assert (Hcursor1 : Int64.add (Int64.repr cursor)
      (Int64.repr (64 - cursor mod 64)) =
      Int64.repr (cursor + (64 - cursor mod 64))).
  { unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity. }
  assert (Hcursor2 : Int64.add
      (Int64.repr (cursor + (64 - cursor mod 64)))
      (Int64.repr (cursor mod 64)) = Int64.repr (cursor + 64)).
  { unfold Int64.add. rewrite !Int64.unsigned_repr by lia. f_equal; lia. }
  assert (Hq : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  pose proof (read8_layout_index cursor ltac:(lia)) as [Hdiv [Hmod _]].
  assert (Hptrfirstbound : 8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned)
    by lia.
  pose proof (read8_layout_pointer edge (cursor / 64) Hq Hptrfirstbound)
    as [HPfirst HPword].
  assert (HPnext : Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))
      (Ptrofs.repr 8) = Ptrofs.repr (edge - 8 * (2 + cursor / 64))).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. f_equal; lia. }
  assert (HLfirst : Mem.load Mint64 mfirst bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (2 + cursor / 64)))) = Some (Vlong low)).
  { erewrite Mem.load_store_other; [|exact SF|].
    - rewrite Ptrofs.unsigned_repr by lia. exact HL.
    - left. congruence. }
  assert (HP8 : Ptrofs.mul (Ptrofs.repr 8)
      (Ptrofs.of_ints (Int.repr 1)) = Ptrofs.repr 8).
  { unfold Ptrofs.mul, Ptrofs.of_ints. vm_compute. reflexivity. }
  assert (HHp : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) = Some (Vlong high)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HH. }
  assert (HOfirst : Mem.load Mint64 mfirst bf (base + 8) =
      Some (Vlong (Int64.repr (cursor + (64 - cursor mod 64))))).
  { exact (Mem.load_store_same _ _ _ _ _ _ SF). }
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read64_layout bf base) (m1 := m)
      (m2 := mf)
      (out := Out_return (Some (Vlong (read64_crossing_at cursor high low), tulong)))
      (vres := Vlong (read64_crossing_at cursor high low)).
  - apply entry_read64_layout.
  - unfold f_simplicity_read64; cbn [fn_body].
    timeout 10 read64_cross_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

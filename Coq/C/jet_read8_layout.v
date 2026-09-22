(** Non-crossing byte reads with arbitrary frame/base addresses and word indices. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_read8 C.jet_read8_position C.jet_frame_layout C.jet_write8.
Require Import C.jet_frame_access C.jet_frame_constants C.jet_frame_arith C.jets.
Require Import C.jet_read8_crossing C.jet_LSBkeep_width.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition le_read8_layout (bf : block) (base : Z) : temp_env :=
  PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps f_simplicity_read8.(fn_temps)).

Lemma entry_read8_layout m bf base :
  function_entry2 ge0 f_simplicity_read8 [Vptr bf (Ptrofs.repr base)]
    m empty_env (le_read8_layout bf base) m.
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

Lemma read8_layout_index cursor : 0 <= cursor <= Int64.max_unsigned - 8 ->
  Int64.divu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor / 64) /\
  Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor mod 64) /\
  Int64.add (Int64.repr cursor) (Int64.repr 8) = Int64.repr (cursor + 8).
Proof.
  intros HC. unfold Int64.divu, Int64.modu, Int64.add.
  rewrite (Int64.unsigned_repr cursor) by lia.
  change (Int64.unsigned (Int64.repr 64)) with 64.
  change (Int64.unsigned (Int64.repr 8)) with 8. repeat split.
Qed.

Lemma read8_layout_pointer edge q :
  0 <= q <= Int64.max_unsigned ->
  8 * (1 + q) <= edge <= Ptrofs.max_unsigned ->
  Ptrofs.sub (Ptrofs.repr edge) (Ptrofs.repr 8) = Ptrofs.repr (edge - 8) /\
  Ptrofs.sub (Ptrofs.repr (edge - 8))
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr q))) =
    Ptrofs.repr (edge - 8 * (1 + q)).
Proof.
  intros HQ HE. split.
  - unfold Ptrofs.sub. rewrite (Ptrofs.unsigned_repr edge) by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. reflexivity.
  - unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
    unfold Ptrofs.mul, Ptrofs.sub.
    rewrite (Ptrofs.unsigned_repr (edge - 8)) by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
    rewrite (Ptrofs.unsigned_repr q) by lia.
    rewrite (Ptrofs.unsigned_repr (8 * q)) by lia.
    f_equal; lia.
Qed.

Ltac readlayout_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int.repr Int.zero_ext Int.or Z.sub Z.add
    Int64.zero_ext Int64.loword Int.shl
    Z.mul Ptrofs.repr Ptrofs.sub Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int.repr Int.zero_ext Int.or Z.sub Z.add
    Int64.zero_ext Int64.loword Int.shl
    Z.mul Ptrofs.repr Ptrofs.sub Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  change (Int.signed (Int.repr 8)) with 8;
  change (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 1)))
    with (Ptrofs.repr 8);
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity | eassumption].

Ltac readlayout_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at; [reflexivity | eassumption]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [readlayout_expr | readlayout_scalar])
        | (eapply eval_Eunop; [readlayout_expr | readlayout_scalar])
        | (eapply eval_Ebinop; [readlayout_expr | readlayout_expr | readlayout_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac readlayout_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [readlayout_stmt | readlayout_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; readlayout_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [readlayout_expr | reflexivity | apply exec_Sskip]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | readlayout_expr | readlayout_expr | apply eval_LSBkeep8_value ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | readlayout_expr | readlayout_scalar
      | eapply assign_frame_offset_at; [eassumption | readlayout_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; readlayout_expr
  end.

Lemma eval_read8_layout_non_crossing m mf bf base bw edge cursor w :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 8 -> cursor mod 64 <= 56 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong w) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + 8))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (read8_at (cursor mod 64) w)).
Proof.
  intros HB HC HR HE [HF HO] HW SF.
  assert (HQ : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia |]. apply Z.div_le_upper_bound; lia. }
  assert (HM : 0 <= cursor mod 64 <= 56) by (pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
  pose proof (read8_layout_index cursor HC) as HI.
  pose proof (read8_layout_pointer edge (cursor / 64) HQ HE) as HP.
  pose proof (read8_cursor_arithmetic (cursor mod 64) HM) as HA.
  assert (HL : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) = Some (Vlong w)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HW. }
  destruct HI as [HIdiv [HImod HIadd]]. destruct HP as [HPfirst HPword].
  destruct HA as [HAdiv [HAmod [HAsub [HAltu [HAsub8 [HAshift HAadd]]]]]].
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read8_at (cursor mod 64) w), tuchar)))
      (vres := Vint (read8_at (cursor mod 64) w)).
  - apply entry_read8_layout.
  - unfold f_simplicity_read8; cbn [fn_body]. timeout 10 readlayout_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_at (cursor mod 64) w))) =
      Some (Vint (read8_at (cursor mod 64) w))).
    unfold read8_at, read8_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

Ltac readlayout_cross_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [readlayout_cross_stmt | readlayout_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; readlayout_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [readlayout_expr | reflexivity | readlayout_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      unfold Swhile; readlayout_cross_stmt
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      eapply exec_Sloop_stop1 with (out' := Out_break);
      [ eapply exec_Sseq_2;
        [ eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
          [readlayout_expr | reflexivity | apply exec_Sbreak]
        | discriminate ]
      | constructor ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | readlayout_expr | readlayout_expr | apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | readlayout_expr | readlayout_scalar
      | eapply assign_frame_offset_at; [eassumption | readlayout_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; readlayout_expr
  end.

Lemma eval_read8_layout_crossing_raw m mm mf bf base bw edge cursor k high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 8 ->
  1 <= k <= 7 -> cursor mod 64 = 64 - k ->
  8 * (2 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + k))) = Some mm ->
  Mem.load Mint64 mm bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Mem.load Mint64 mm bf (base + 8) = Some (Vlong (Int64.repr (cursor + k))) ->
  Mem.store Mint64 mm bf (base + 8) (Vlong (Int64.repr (cursor + 8))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (read8_crossing_result k high low)).
Proof.
  intros HB HC HK HR HE [HF HO] HH SM HL HOm SF.
  assert (HQ : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia |]. apply Z.div_le_upper_bound; lia. }
  pose proof (read8_layout_index cursor HC) as [HIdiv [HImod HIadd]].
  rewrite HR in HImod.
  pose proof (read8_layout_pointer edge (cursor / 64) HQ ltac:(lia)) as [HPfirst HPword].
  assert (HPnext : Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))
      (Ptrofs.repr 8) = Ptrofs.repr (edge - 8 * (2 + cursor / 64))).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. f_equal; lia. }
  pose proof (read8_crossing_arithmetic k HK)
    as [HAdiv [HAmod [HAsub [HAltu [HAsub8 [HAshift [HAadd [HALtu [HASub [HAShift HAAdd]]]]]]]]]].
  assert (HStep : Int64.add (Int64.repr cursor) (Int64.repr k) = Int64.repr (cursor + k)).
  { unfold Int64.add. rewrite (Int64.unsigned_repr cursor) by lia.
    rewrite cursor_unsigned by lia. reflexivity. }
  assert (HFinal : Int64.add (Int64.repr (cursor + k)) (Int64.repr (8 - k)) =
      Int64.repr (cursor + 8)).
  { unfold Int64.add. rewrite (Int64.unsigned_repr (cursor + k)) by lia.
    rewrite cursor_unsigned by lia. f_equal; lia. }
  assert (HHp : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) = Some (Vlong high)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HH. }
  assert (HLp : Mem.load Mint64 mm bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (2 + cursor / 64)))) = Some (Vlong low)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HL. }
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read8_crossing_result k high low), tuchar)))
      (vres := Vint (read8_crossing_result k high low)).
  - apply entry_read8_layout.
  - unfold f_simplicity_read8; cbn [fn_body]. timeout 10 readlayout_cross_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_crossing_result k high low))) =
      Some (Vint (read8_crossing_result k high low))).
    unfold read8_crossing_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

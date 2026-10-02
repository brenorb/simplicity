(** Actual read4 execution for arbitrary non-crossing input frame layouts.
    This is a reader milestone, not a total reader or a covered jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_read8 C.jet_write8 C.jet_frame_layout.
Require Import C.jet_frame_access C.jet_frame_constants C.jet_frame_arith C.jets.
Require Import C.jet_read8_layout C.jet_LSBkeep_width.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition read4_result (w : int64) : int :=
  Int.zero_ext 8 (Int.or Int.zero
    (Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.and w (Int64.repr 15)))))).
Definition read4_at cursor w := read4_result (Int64.shru w (Int64.repr (60 - cursor))).

Lemma eval_LSBkeep4_value m w :
  Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    [Vlong w; Vlong (Int64.repr 4)] E0 m (Vlong (Int64.and w (Int64.repr 15))).
Proof.
  replace (Int64.and w (Int64.repr 15)) with (Int64.zero_ext 4 w).
  - apply eval_keep_width; lia.
  - rewrite <- keep_mask by lia. reflexivity.
Qed.

Lemma read4_cursor_arithmetic cursor : 0 <= cursor <= 60 ->
  Int64.divu (Int64.repr cursor) (Int64.repr 64) = Int64.zero /\
  Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr cursor /\
  Int64.sub (Int64.repr 64) (Int64.repr cursor) = Int64.repr (64 - cursor) /\
  Int64.ltu (Int64.repr (64 - cursor)) (Int64.repr 4) = false /\
  Int64.sub (Int64.repr (64 - cursor)) (Int64.repr 4) = Int64.repr (60 - cursor) /\
  Int64.ltu (Int64.repr (60 - cursor)) Int64.iwordsize = true /\
  Int64.add (Int64.repr cursor) (Int64.repr 4) = Int64.repr (cursor + 4).
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

Definition le_read4_layout (bf : block) (base : Z) : temp_env :=
  PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps f_simplicity_read4.(fn_temps)).

Lemma entry_read4_layout m bf base :
  function_entry2 ge0 f_simplicity_read4 [Vptr bf (Ptrofs.repr base)]
    m empty_env (le_read4_layout bf base) m.
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

Lemma read4_layout_index cursor : 0 <= cursor <= Int64.max_unsigned - 4 ->
  Int64.divu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor / 64) /\
  Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor mod 64) /\
  Int64.add (Int64.repr cursor) (Int64.repr 4) = Int64.repr (cursor + 4).
Proof.
  intros HC. unfold Int64.divu, Int64.modu, Int64.add.
  rewrite (Int64.unsigned_repr cursor) by lia.
  change (Int64.unsigned (Int64.repr 64)) with 64.
  change (Int64.unsigned (Int64.repr 4)) with 4. repeat split.
Qed.

Ltac read4layout_scalar :=
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
  change (Int.signed (Int.repr 4)) with 4;
  change (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 1)))
    with (Ptrofs.repr 8);
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity | eassumption].

Ltac read4layout_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at; [reflexivity | eassumption]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [read4layout_expr | read4layout_scalar])
        | (eapply eval_Eunop; [read4layout_expr | read4layout_scalar])
        | (eapply eval_Ebinop; [read4layout_expr | read4layout_expr | read4layout_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac read4layout_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [read4layout_stmt | read4layout_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read4layout_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [read4layout_expr | reflexivity | apply exec_Sskip]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | read4layout_expr | read4layout_expr | apply eval_LSBkeep4_value ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | read4layout_expr | read4layout_scalar
      | eapply assign_frame_offset_at; [eassumption | read4layout_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read4layout_expr
  end.

Lemma eval_read4_layout_non_crossing m mf bf base bw edge cursor w :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 4 -> cursor mod 64 <= 60 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong w) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + 4))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read4)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (read4_at (cursor mod 64) w)).
Proof.
  intros HB HC HR HE [HF HO] HW SF.
  assert (HQ : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia |]. apply Z.div_le_upper_bound; lia. }
  assert (HM : 0 <= cursor mod 64 <= 60) by (pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
  pose proof (read4_layout_index cursor HC) as HI.
  pose proof (read8_layout_pointer edge (cursor / 64) HQ HE) as HP.
  pose proof (read4_cursor_arithmetic (cursor mod 64) HM) as HA.
  assert (HL : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) = Some (Vlong w)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HW. }
  destruct HI as [HIdiv [HImod HIadd]]. destruct HP as [HPfirst HPword].
  destruct HA as [HAdiv [HAmod [HAsub [HAltu [HAsub8 [HAshift HAadd]]]]]].
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read4_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read4_at (cursor mod 64) w), tuchar)))
      (vres := Vint (read4_at (cursor mod 64) w)).
  - apply entry_read4_layout.
  - unfold f_simplicity_read4; cbn [fn_body]. timeout 10 read4layout_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read4_at (cursor mod 64) w))) =
      Some (Vint (read4_at (cursor mod 64) w))).
    unfold read4_at, read4_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.


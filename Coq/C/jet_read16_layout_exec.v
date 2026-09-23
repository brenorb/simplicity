(** Initial execution kernel for the generated 16-bit frame reader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access.
Require Import C.jet_frame_constants C.jet_frame_arith C.jet_LSBkeep_width.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition le_read16_layout (bf : block) (base : Z) : temp_env :=
  PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps f_simplicity_read16.(fn_temps)).

Lemma entry_read16_layout m bf base :
  function_entry2 ge0 f_simplicity_read16 [Vptr bf (Ptrofs.repr base)]
    m empty_env (le_read16_layout bf base) m.
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

Definition read16_at_zero (high : int64) : int64 :=
  Int64.zero_ext 16 (Int64.shru high (Int64.repr 48)).

Definition read16_at_56 (high low : int64) : int64 :=
  Int64.or
    (Int64.shl (Int64.zero_ext 8 high) (Int64.repr 8))
    (Int64.zero_ext 8 (Int64.shru low (Int64.repr 56))).

Lemma exec_read16_while_false le m cond body v :
  eval_expr ge0 empty_env le m cond v ->
  bool_val v (typeof cond) m = Some false ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m
    (Swhile cond body) E0 le m Out_normal.
Proof.
  intros HE HB. unfold Swhile.
  eapply ClightBigstep.exec_Sloop_stop1 with (out' := Out_break).
  - eapply ClightBigstep.exec_Sseq_2.
    + eapply ClightBigstep.exec_Sifthenelse with (v1 := v) (b := false);
        [exact HE | exact HB | apply ClightBigstep.exec_Sbreak].
    + discriminate.
  - constructor.
Qed.

Ltac read16_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int64.or Int.repr Int.zero_ext Int.or Z.sub Z.add
    Int64.zero_ext Int64.loword Int.shl Int64.shl
    Z.mul Ptrofs.repr Ptrofs.sub Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int64.or Int.repr Int.zero_ext Int.or Z.sub Z.add
    Int64.zero_ext Int64.loword Int.shl Int64.shl
    Z.mul Ptrofs.repr Ptrofs.sub Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  try change (Int.signed (Int.repr 16)) with 16;
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity | eassumption].

Ltac read16_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at; [reflexivity | eassumption]]
        | (eapply eval_Etempvar; cbn; try rewrite Int64.or_zero_l; reflexivity)
        | (eapply eval_Ecast; [read16_expr | read16_scalar])
        | (eapply eval_Eunop; [read16_expr | read16_scalar])
        | (eapply eval_Ebinop; [read16_expr | read16_expr | read16_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac read16_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [read16_stmt | read16_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read16_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [read16_expr | reflexivity | apply exec_Sskip]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | read16_expr | read16_expr | apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | read16_expr | read16_scalar
      | eapply assign_frame_offset_at; [eassumption | read16_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read16_expr
  end.

Ltac read16_cross_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [read16_cross_stmt | read16_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read16_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [read16_expr | reflexivity | read16_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      eapply exec_read16_while_false; [read16_expr | read16_scalar]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | read16_expr | read16_expr | apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | read16_expr | read16_scalar
      | eapply assign_frame_offset_at; [eassumption | read16_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read16_expr
  end.

Lemma eval_read16_layout_zero_cursor m mf bf base bw high :
  frame_base_valid base ->
  frame_fields_at m bf base bw 16 0 ->
  Mem.load Mint64 m bw 8 = Some (Vlong high) ->
  Mem.valid_access m Mint64 bf (base + 8) Writable ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr 16)) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read16)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong (read16_at_zero high)).
Proof.
  intros HB [HE HO] HH PW SF.
  assert (HL : (le_read16_layout bf base)!_frame =
    Some (Vptr bf (Ptrofs.repr base))).
  { unfold le_read16_layout. rewrite PTree.gss. reflexivity. }
  assert (HLw : Mem.load Mint64 m bw 8 = Some (Vlong high)) by exact HH.
  assert (Hptr : Ptrofs.sub (Ptrofs.repr 16) (Ptrofs.repr 8) = Ptrofs.repr 8).
  { unfold Ptrofs.sub. vm_compute. reflexivity. }
  assert (Hmod : Int64.modu (Int64.repr 0) (Int64.repr 64) = Int64.zero)
    by reflexivity.
  assert (Hdiv : Int64.divu (Int64.repr 0) (Int64.repr 64) = Int64.zero)
    by reflexivity.
  assert (Hcursor : Int64.add (Int64.repr 0) (Int64.repr 16) = Int64.repr 16)
    by reflexivity.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read16_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vlong (read16_at_zero high), tulong)))
      (vres := Vlong (read16_at_zero high)).
  - apply entry_read16_layout.
  - unfold f_simplicity_read16; cbn [fn_body].
    timeout 10 read16_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Lemma read16_layout_arithmetic cursor :
  0 <= cursor <= Int64.max_unsigned - 16 -> cursor mod 64 <= 48 ->
  Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64) /\
  Int64.ltu (Int64.repr (64 - cursor mod 64)) (Int64.repr 16) = false /\
  Int64.sub (Int64.repr (64 - cursor mod 64)) (Int64.repr 16) =
      Int64.repr (48 - cursor mod 64) /\
  Int64.add (Int64.repr cursor) (Int64.repr 16) = Int64.repr (cursor + 16).
Proof.
  intros HC HR. assert (HM : 0 <= cursor mod 64 < 64).
  { apply Z.mod_pos_bound; lia. }
  assert (Hshift : Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64))
    by exact (@cursor_sub 64 (cursor mod 64) ltac:(lia) ltac:(lia)).
  assert (Hremain : Int64.sub (Int64.repr (64 - cursor mod 64))
      (Int64.repr 16) = Int64.repr (48 - cursor mod 64)).
  { pose proof (@cursor_sub (64 - cursor mod 64) 16 ltac:(lia) ltac:(lia)) as H.
    replace (64 - cursor mod 64 - 16) with (48 - cursor mod 64) in H by lia.
    exact H. }
  split; [exact Hshift|]. split.
  - unfold Int64.ltu. rewrite !cursor_unsigned by lia.
    rewrite zlt_false by lia. reflexivity.
  - split; [exact Hremain|].
    unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity.
Qed.

Lemma eval_read16_layout_cursor56 m m64 mf bf base bw high low :
  frame_base_valid base ->
  frame_fields_at m bf base bw 16 56 ->
  Mem.load Mint64 m bw 8 = Some (Vlong high) ->
  Mem.load Mint64 m bw 0 = Some (Vlong low) ->
  bf <> bw ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr 64)) = Some m64 ->
  Mem.load Mint64 m64 bw 0 = Some (Vlong low) ->
  Mem.store Mint64 m64 bf (base + 8) (Vlong (Int64.repr 72)) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read16)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong (read16_at_56 high low)).
Proof.
  intros HB [HE HO] HH HL Hsep S64 HL64 S72.
  assert (Hedge64 : Mem.load Mptr m64 bf base =
      Some (Vptr bw (Ptrofs.repr 16))).
  { erewrite Mem.load_store_other; [exact HE | exact S64 |].
    right; left; simpl; lia. }
  assert (Hoffset64 : Mem.load Mint64 m64 bf (base + 8) =
      Some (Vlong (Int64.repr 64))).
  { exact (Mem.load_store_same _ _ _ _ _ _ S64). }
  assert (Hedge72 : Mem.load Mptr mf bf base =
      Some (Vptr bw (Ptrofs.repr 16))).
  { erewrite Mem.load_store_other; [exact Hedge64 | exact S72 |].
    right; left; simpl; lia. }
  assert (Hoffset72 : Mem.load Mint64 mf bf (base + 8) =
      Some (Vlong (Int64.repr 72))).
  { exact (Mem.load_store_same _ _ _ _ _ _ S72). }
  assert (Hdiv : Int64.divu (Int64.repr 56) (Int64.repr 64) = Int64.zero)
    by reflexivity.
  assert (Hmod : Int64.modu (Int64.repr 56) (Int64.repr 64) = Int64.repr 56)
    by reflexivity.
  assert (Hshift : Int64.sub (Int64.repr 64) (Int64.repr 56) = Int64.repr 8)
    by reflexivity.
  assert (Hremain : Int64.sub (Int64.repr 16) (Int64.repr 8) = Int64.repr 8)
    by reflexivity.
  assert (Hlowshift : Int64.sub (Int64.repr 64) (Int64.repr 8) = Int64.repr 56)
    by reflexivity.
  assert (Hlt : Int64.ltu (Int64.repr 8) (Int64.repr 16) = true)
    by reflexivity.
  assert (Hltloop : Int64.ltu (Int64.repr 64) (Int64.repr 8) = false)
    by reflexivity.
  assert (Hoffset1 : Int64.add (Int64.repr 56) (Int64.repr 8) = Int64.repr 64)
    by reflexivity.
  assert (Hoffset2 : Int64.add (Int64.repr 64) (Int64.repr 8) = Int64.repr 72)
    by reflexivity.
  assert (Hptr : Ptrofs.sub (Ptrofs.repr 16) (Ptrofs.repr 8) = Ptrofs.repr 8)
    by (unfold Ptrofs.sub; vm_compute; reflexivity).
  assert (Hptr0 : Ptrofs.sub (Ptrofs.repr 8) (Ptrofs.repr 8) = Ptrofs.zero)
    by (unfold Ptrofs.sub; vm_compute; reflexivity).
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read16_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vlong (read16_at_56 high low), tulong)))
      (vres := Vlong (read16_at_56 high low)).
  - apply entry_read16_layout.
  - unfold f_simplicity_read16; cbn [fn_body].
    timeout 10 read16_cross_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

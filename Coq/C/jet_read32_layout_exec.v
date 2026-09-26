(** Actual generated read32 Clight execution for non-crossing cursors. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access.
Require Import C.jet_frame_constants C.jet_frame_arith C.jet_LSBkeep_width.
Require Import C.jet_read8_layout C.jet_read16_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition le_read32_layout (bf : block) (base : Z) : temp_env :=
  PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps f_simplicity_read32.(fn_temps)).

Lemma entry_read32_layout m bf base :
  function_entry2 ge0 f_simplicity_read32 [Vptr bf (Ptrofs.repr base)]
    m empty_env (le_read32_layout bf base) m.
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

Definition read32_non_crossing_at (cursor : Z) (high : int64) : int64 :=
  Int64.zero_ext 32
    (Int64.shru high (Int64.repr (32 - cursor mod 64))).

Lemma eval_read32_final_shift le m cursor high :
  le!_t'4 = Some (Vlong high) ->
  le!_frame_shift = Some (Vlong (Int64.repr (64 - cursor mod 64))) ->
  le!_n = Some (Vlong (Int64.repr 32)) ->
  Int64.sub (Int64.repr (64 - cursor mod 64)) (Int64.repr 32) =
    Int64.repr (32 - cursor mod 64) ->
  Int64.ltu (Int64.repr (32 - cursor mod 64)) Int64.iwordsize = true ->
  eval_expr ge0 empty_env le m
    (Ecast
      (Ebinop Oshr (Etempvar _t'4 tulong)
        (Ebinop Osub (Etempvar _frame_shift tulong)
          (Etempvar _n tulong) tulong) tulong) tulong)
    (Vlong (Int64.shru high (Int64.repr (32 - cursor mod 64)))).
Proof.
  intros HT Hshift Hn Hsub Hvalid.
  eapply eval_Ecast with
    (v1 := Vlong (Int64.shru high (Int64.repr (32 - cursor mod 64)))).
  - eapply eval_Ebinop with
      (v1 := Vlong high)
      (v2 := Vlong (Int64.repr (32 - cursor mod 64))).
    + eapply eval_Etempvar. exact HT.
    + eapply eval_Ebinop with
        (v1 := Vlong (Int64.repr (64 - cursor mod 64)))
        (v2 := Vlong (Int64.repr 32)).
      * eapply eval_Etempvar. exact Hshift.
      * eapply eval_Etempvar. exact Hn.
      * change
          (Some (Vlong (Int64.sub (Int64.repr (64 - cursor mod 64))
            (Int64.repr 32))) =
           Some (Vlong (Int64.repr (32 - cursor mod 64)))).
        rewrite Hsub. reflexivity.
    + change
        ((if Int64.ltu (Int64.repr (32 - cursor mod 64)) Int64.iwordsize
          then Some (Vlong (Int64.shru high (Int64.repr (32 - cursor mod 64))))
          else None) =
         Some (Vlong (Int64.shru high (Int64.repr (32 - cursor mod 64))))).
      rewrite Hvalid. reflexivity.
  - reflexivity.
Qed.

Ltac read32_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int64.or Int.repr Int.zero_ext Int.or Z.sub Z.add
    Int64.zero_ext Int64.loword Int.shl Int64.shl
    Z.mul Ptrofs.repr Ptrofs.sub Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shru Int64.and Int64.or Int.repr Int.zero_ext Int.or Z.sub Z.add
    Int64.zero_ext Int64.loword Int.shl Int64.shl
    Z.mul Ptrofs.repr Ptrofs.sub Ptrofs.mul Ptrofs.of_int64 Ptrofs.unsigned];
  try change (Int.signed (Int.repr 32)) with 32;
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity | eassumption].

Ltac read32_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_word_at;
            [repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
             first [reflexivity | eassumption]
            | repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
              first [reflexivity | eassumption]]]
        | solve [eapply eval_read32_final_shift;
            [reflexivity | reflexivity | reflexivity | eassumption | eassumption]]
        | solve [eapply eval_Etempvar; reflexivity]
        | (eapply eval_Etempvar; cbn; try rewrite Int64.or_zero_l; reflexivity)
        | (eapply eval_Ecast; [read32_expr | read32_scalar])
        | (eapply eval_Eunop; [read32_expr | read32_scalar])
        | (eapply eval_Ebinop; [read32_expr | read32_expr | read32_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac read32_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [read32_stmt | read32_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read32_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [first [eapply eval_read16_unsigned_lt_false;
                  [reflexivity | reflexivity | eassumption]
               | read32_expr]
        | reflexivity | apply exec_Sskip]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      eapply exec_read16_while_false; [read32_expr | read32_scalar]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | read32_expr | read32_expr | apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | read32_expr | read32_scalar
      | eapply assign_frame_offset_at; [eassumption | read32_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read32_expr
  end.

Lemma read32_layout_arithmetic cursor :
  0 <= cursor <= Int64.max_unsigned - 32 -> cursor mod 64 <= 32 ->
  Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64) /\
  Int64.ltu (Int64.repr (64 - cursor mod 64)) (Int64.repr 32) = false /\
  Int64.sub (Int64.repr (64 - cursor mod 64)) (Int64.repr 32) =
      Int64.repr (32 - cursor mod 64) /\
  Int64.add (Int64.repr cursor) (Int64.repr 32) = Int64.repr (cursor + 32).
Proof.
  intros HC HR. assert (HM : 0 <= cursor mod 64 < 64).
  { apply Z.mod_pos_bound; lia. }
  assert (Hshift : Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64))
    by exact (@cursor_sub 64 (cursor mod 64) ltac:(lia) ltac:(lia)).
  assert (Hremain : Int64.sub (Int64.repr (64 - cursor mod 64))
      (Int64.repr 32) = Int64.repr (32 - cursor mod 64)).
  { pose proof (@cursor_sub (64 - cursor mod 64) 32 ltac:(lia) ltac:(lia)) as H.
    replace (64 - cursor mod 64 - 32) with (32 - cursor mod 64) in H by lia.
    exact H. }
  split; [exact Hshift|]. split.
  - unfold Int64.ltu. rewrite !cursor_unsigned by lia.
    rewrite zlt_false by lia. reflexivity.
  - split; [exact Hremain|].
    unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity.
Qed.

Lemma eval_read32_layout_non_crossing m mf bf base bw edge cursor high :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 32 ->
  cursor mod 64 <= 32 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + 32))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read32)
    [Vptr bf (Ptrofs.repr base)] E0 mf
    (Vlong (read32_non_crossing_at cursor high)).
Proof.
  intros HB HC HR HE [HF HO] HH SF.
  assert (Hq : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  pose proof (read8_layout_index cursor ltac:(lia)) as [Hdiv [Hmod _]].
  destruct (read32_layout_arithmetic cursor HC HR)
    as [Hshift [Hlt [Hfinalshift Hcursor]]].
  assert (HM : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hshiftvalid :
    Int64.ltu (Int64.repr (32 - cursor mod 64)) Int64.iwordsize = true).
  { unfold Int64.ltu. change Int64.iwordsize with (Int64.repr 64).
    rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    rewrite zlt_true by lia. reflexivity. }
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
    with (e := empty_env) (le1 := le_read32_layout bf base) (m1 := m)
      (m2 := mf)
      (out := Out_return
        (Some (Vlong (read32_non_crossing_at cursor high), tulong)))
      (vres := Vlong (read32_non_crossing_at cursor high)).
  - apply entry_read32_layout.
  - unfold f_simplicity_read32; cbn [fn_body].
    timeout 10 read32_stmt.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

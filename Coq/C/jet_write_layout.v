(** Shared address arithmetic and expression rules for generated frame writers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_frame_arith C.jet_LSBclear_width C.jet_LSBkeep_width C.jet_crossing_arith.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition write_word_address edge cursor := edge + 8 * ((cursor - 1) / 64).
Definition write_word_shift cursor := 1 + (cursor - 1) mod 64.

Lemma write_layout_index cursor : 1 <= cursor <= Int64.max_unsigned ->
  0 <= (cursor - 1) / 64 <= Int64.max_unsigned /\
  1 <= write_word_shift cursor <= 64 /\
  Int64.sub (Int64.repr cursor) (Int64.repr 1) = Int64.repr (cursor - 1) /\
  Int64.divu (Int64.repr (cursor - 1)) (Int64.repr 64) = Int64.repr ((cursor - 1) / 64) /\
  Int64.modu (Int64.repr (cursor - 1)) (Int64.repr 64) = Int64.repr ((cursor - 1) mod 64) /\
  Int64.add (Int64.repr ((cursor - 1) mod 64)) (Int64.repr 1) = Int64.repr (write_word_shift cursor).
Proof.
  intros HC. pose proof (Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)) as HR.
  split.
  - split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia].
  - split; [unfold write_word_shift; lia|]. split.
    + unfold Int64.sub. rewrite (Int64.unsigned_repr cursor) by lia.
      change (Int64.unsigned (Int64.repr 1)) with 1. reflexivity.
    + split.
      * unfold Int64.divu. rewrite (Int64.unsigned_repr (cursor - 1)) by lia. reflexivity.
      * split.
        -- unfold Int64.modu. rewrite (Int64.unsigned_repr (cursor - 1)) by lia. reflexivity.
        -- unfold Int64.add. rewrite cursor_unsigned by lia.
           change (Int64.unsigned (Int64.repr 1)) with 1.
           unfold write_word_shift. f_equal; lia.
Qed.

Lemma write_layout_pointer edge q :
  0 <= q <= Int64.max_unsigned -> 0 <= edge -> edge + 8 * q <= Ptrofs.max_unsigned ->
  Ptrofs.add (Ptrofs.repr edge)
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr q))) = Ptrofs.repr (edge + 8 * q).
Proof.
  intros HQ HE HA. unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  unfold Ptrofs.add, Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr edge) by lia.
  change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
  rewrite (Ptrofs.unsigned_repr q) by lia.
  rewrite (Ptrofs.unsigned_repr (8 * q)) by lia. reflexivity.
Qed.

Ltac writelayout_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shl Int64.shru Int64.or Int64.loword Int64.zero_ext
    Int.shr Int.repr Z.sub Z.add Z.mul Ptrofs.repr Ptrofs.unsigned
    Ptrofs.add Ptrofs.sub Ptrofs.mul Ptrofs.of_int64];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shl Int64.shru Int64.or Int64.loword Int64.zero_ext
    Int.shr Int.repr Z.sub Z.add Z.mul Ptrofs.repr Ptrofs.unsigned
    Ptrofs.add Ptrofs.sub Ptrofs.mul Ptrofs.of_int64];
  change (Int.signed (Int.repr 1)) with 1;
  change (Int.signed (Int.repr 8)) with 8;
  change (Int64.repr (Int.signed Int.zero)) with Int64.zero;
  change (Int64.repr (Int.unsigned Int.one)) with Int64.one;
  change (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 1))) with (Ptrofs.repr 8);
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  try rewrite clear_entire_word; try rewrite Int64.or_zero; try rewrite Int64.or_zero_l;
  first [reflexivity | eassumption].

Ltac writelayout_expr :=
  first [ solve [apply eval_generated_uword_bits]
        | solve [eapply eval_frame_edge_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_frame_offset_at; [eassumption | reflexivity | eassumption]]
        | solve [eapply eval_Elvalue;
            [eapply eval_Ederef; eapply eval_Etempvar; reflexivity
            | eapply deref_loc_value; [reflexivity | eassumption]]]
        | (eapply eval_Etempvar; reflexivity)
        | (eapply eval_Ecast; [writelayout_expr | writelayout_scalar])
        | (eapply eval_Eunop; [writelayout_expr | writelayout_scalar])
        | (eapply eval_Ebinop; [writelayout_expr | writelayout_expr | writelayout_scalar])
        | apply eval_Econst_int | apply eval_Econst_long ].

Ltac writelayout_call funbody sym funproof :=
  eapply call_word_helper with (f := funbody);
  [reflexivity | reflexivity | reflexivity | apply sym | apply funproof
  | writelayout_expr | writelayout_expr
  | first [apply eval_clear_width; lia | apply eval_keep_width; lia]].

Ltac writelayout_assign :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [apply eval_frame_offset_lvalue_at; reflexivity | writelayout_expr | writelayout_scalar
      | eapply assign_frame_offset_at; [eassumption | first [eassumption | writelayout_scalar]]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Ederef _ _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [eapply eval_Ederef; eapply eval_Etempvar; reflexivity
      | writelayout_expr | writelayout_scalar
      | apply assign_frame_word_at; first [eassumption | writelayout_scalar]]
  end.

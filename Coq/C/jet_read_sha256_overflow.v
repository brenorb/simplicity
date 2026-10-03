(** Actual overflow-store and return suffix of read_sha256_context.
    Both comparison outcomes are retained; this is an internal suffix proof,
    not yet a complete function or public jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_sha256_context_fields C.jet_sha256_max_counter.
Require Import C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_read_overflow count := Int64.cmpu Cle (Int64.repr 36028797018963968) count.

Lemma sha256_read_overflow_false count :
  sha256_read_overflow count = false <-> Int64.unsigned count < 36028797018963968.
Proof.
  unfold sha256_read_overflow, Int64.cmpu, Int64.ltu.
  change (Int64.unsigned (Int64.repr 36028797018963968)) with 36028797018963968.
  destruct (zlt (Int64.unsigned count) 36028797018963968); cbn; intuition congruence.
Qed.

Lemma sha256_read_overflow_true count :
  sha256_read_overflow count = true <-> 36028797018963968 <= Int64.unsigned count.
Proof.
  unfold sha256_read_overflow, Int64.cmpu, Int64.ltu.
  change (Int64.unsigned (Int64.repr 36028797018963968)) with 36028797018963968.
  destruct (zlt (Int64.unsigned count) 36028797018963968); cbn;
    split; intro H; try discriminate; try reflexivity; lia.
Qed.
Definition sha256_read_overflow_stmt :=
  Ssequence
    (Ssequence (Sset _t'3 (Evar _sha256_max_counter tulong))
      (Sassign (sha256_context_field_expr CtxOverflow _ctx)
        (Ebinop Ole (Ebinop Oshr (Etempvar _t'3 tulong)
          (Econst_int (Int.repr 6) tint) tulong)
          (Etempvar _compressionCount tulong) tint)))
    (Ssequence (Sset _t'2 (sha256_context_field_expr CtxOverflow _ctx))
      (Sreturn (Some (Eunop Onotbool (Etempvar _t'2 tbool) tint)))).

Lemma sha256_read_overflow_actual_suffix :
  match fn_body f_simplicity_read_sha256_context with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ suffix))) => suffix
  | _ => Sskip
  end = sha256_read_overflow_stmt.
Proof. reflexivity. Qed.

Lemma exec_sha256_read_overflow_store e le m mf bc base count :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  le!_t'3 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  Mem.store Mint8unsigned m bc (base + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mf ->
  Clight2.exec_stmt ge0 e le m
    (Sassign (sha256_context_field_expr CtxOverflow _ctx)
      (Ebinop Ole (Ebinop Oshr (Etempvar _t'3 tulong)
        (Econst_int (Int.repr 6) tint) tulong)
        (Etempvar _compressionCount tulong) tint)) E0 le mf Out_normal.
Proof.
  intros HB HM HC HCount HT HS.
  eapply exec_Sassign_value with (v := Vint (bit_int (sha256_read_overflow count)))
    (v2 := Vint (bit_int (sha256_read_overflow count)))
    (b := bc) (ofs := Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 80)).
  - apply eval_sha256_context_field_lvalue; exact HC.
  - eapply eval_Ebinop with (v1 := Vlong (Int64.repr 36028797018963968)) (v2 := Vlong count).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr 2305843009213693952)) (v2 := Vint (Int.repr 6));
        [apply eval_Etempvar; exact HT|apply eval_Econst_int|reflexivity].
    + apply eval_Etempvar; exact HCount.
    + change (Some (Val.of_bool (sha256_read_overflow count)) =
        Some (Vint (bit_int (sha256_read_overflow count)))).
      destruct (sha256_read_overflow count); reflexivity.
  - destruct (sha256_read_overflow count); reflexivity.
  - apply assign_loc_value with (chunk := Mint8unsigned); [reflexivity|].
    unfold Mem.storev. change (Mem.store Mint8unsigned m bc
      (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset CtxOverflow))))
      (Vint (bit_int (sha256_read_overflow count))) = Some mf).
    rewrite sha256_context_address by assumption; exact HS.
Qed.

Theorem exec_sha256_read_overflow_from_observation e le m bc base count :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  e!_sha256_max_counter = None ->
  Mem.load Mint64 m (jet_symbol_block _sha256_max_counter) 0 =
    Some (Vlong (Int64.repr 2305843009213693952)) ->
  bc <> jet_symbol_block _sha256_max_counter ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  Mem.valid_access m Mint8unsigned bc (base + 80) Writable ->
  exists mf lef,
    Clight2.exec_stmt ge0 e le m sha256_read_overflow_stmt E0 lef mf
      (Out_return (Some (Vint (bit_int (negb (sha256_read_overflow count))), tint))) /\
    Mem.store Mint8unsigned m bc (base + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mf /\
    Mem.load Mint8unsigned mf bc (base + 80) = Some (Vint (bit_int (sha256_read_overflow count))) /\
    Mem.load Mint64 mf (jet_symbol_block _sha256_max_counter) 0 =
      Some (Vlong (Int64.repr 2305843009213693952)).
Proof.
  intros HB HM HE HGlobal HOther HC HCount HW.
  destruct (Mem.valid_access_store m Mint8unsigned bc (base + 80)
    (Vint (bit_int (sha256_read_overflow count))) HW) as [mf HS].
  set (le1 := PTree.set _t'3 (Vlong (Int64.repr 2305843009213693952)) le).
  set (le2 := PTree.set _t'2 (Vint (bit_int (sha256_read_overflow count))) le1).
  assert (HL : Mem.load Mint8unsigned mf bc (base + 80) =
    Some (Vint (bit_int (sha256_read_overflow count)))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ HS).
    destruct (sha256_read_overflow count); reflexivity. }
  exists mf, le2. split.
  - unfold sha256_read_overflow_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mf).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * apply exec_set. eapply eval_Elvalue.
        -- apply eval_Evar_global; [exact HE|exact sha256_max_counter_symbol].
        -- apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HGlobal].
      * eapply exec_sha256_read_overflow_store; [exact HB|exact HM|
          unfold le1; rewrite PTree.gso by discriminate; exact HC|
          unfold le1; rewrite PTree.gso by discriminate; exact HCount|
          unfold le1; apply PTree.gss|exact HS].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mf).
      * apply exec_set. eapply eval_sha256_context_field with (chunk := Mint8unsigned);
          [exact HB|exact HM|reflexivity|
           unfold le1; rewrite PTree.gso by discriminate; exact HC|exact HL].
      * apply exec_Sreturn_some. eapply eval_Eunop;
          [apply eval_Etempvar; unfold le2; apply PTree.gss|].
        destruct (sha256_read_overflow count); reflexivity.
  - split; [exact HS|]. split; [exact HL|].
    erewrite Mem.load_store_other; [exact HGlobal|exact HS|left; congruence].
Qed.

(** Stronger provenance wrapper; callers with load framing alone can instead
    use the observation consumer after deriving separation in initial memory. *)
Theorem exec_sha256_read_overflow_from_memory e le m bc base count :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  e!_sha256_max_counter = None -> sha256_max_counter_at m ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  Mem.valid_access m Mint8unsigned bc (base + 80) Writable ->
  exists mf lef,
    Clight2.exec_stmt ge0 e le m sha256_read_overflow_stmt E0 lef mf
      (Out_return (Some (Vint (bit_int (negb (sha256_read_overflow count))), tint))) /\
    Mem.store Mint8unsigned m bc (base + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mf /\
    Mem.load Mint8unsigned mf bc (base + 80) = Some (Vint (bit_int (sha256_read_overflow count))) /\
    sha256_max_counter_at mf.
Proof.
  intros HB HM HE HGlobal HC HCount HW.
  destruct (exec_sha256_read_overflow_from_observation e le m bc base count
    HB HM HE (proj1 HGlobal) (sha256_max_counter_writable_other _ _ _ _ HGlobal HW)
    HC HCount HW) as (mf & lef & HExec & HS & HL & HLimit).
  exists mf, lef. split; [exact HExec|]. split; [exact HS|]. split; [exact HL|].
  eapply sha256_max_counter_store; eauto.
Qed.

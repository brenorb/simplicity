(** Actual counter reconstruction in read_sha256_context. Keep the machine
    expression on all inputs, including counts that will later overflow. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_sha256_context_fields C.jet_sha256_max_counter.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_read_counter count len :=
  Int64.add (Int64.shl (Int64.mul count (Int64.repr 1)) (Int64.repr 6)) len.
Definition sha256_read_counter_stmt :=
  Ssequence (Sset _t'5 (Evar _len tulong))
    (Sassign (sha256_context_field_expr CtxCounter _ctx)
      (Ebinop Oadd
        (Ebinop Oshl (Ebinop Omul (Etempvar _compressionCount tulong)
          (Econst_int (Int.repr 1) tuint) tulong)
          (Econst_int (Int.repr 6) tint) tulong)
        (Etempvar _t'5 tulong) tulong)).

Lemma sha256_read_counter_actual_stmt :
  match fn_body f_simplicity_read_sha256_context with
  | Ssequence _ (Ssequence _ (Ssequence stmt _)) => stmt
  | _ => Sskip
  end = sha256_read_counter_stmt.
Proof. reflexivity. Qed.

Lemma exec_sha256_read_counter_store e le m mf bc base count len :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) -> le!_t'5 = Some (Vlong len) ->
  Mem.store Mint64 m bc (base + 8) (Vlong (sha256_read_counter count len)) = Some mf ->
  Clight2.exec_stmt ge0 e le m
    (Sassign (sha256_context_field_expr CtxCounter _ctx)
      (Ebinop Oadd
        (Ebinop Oshl (Ebinop Omul (Etempvar _compressionCount tulong)
          (Econst_int (Int.repr 1) tuint) tulong)
          (Econst_int (Int.repr 6) tint) tulong)
        (Etempvar _t'5 tulong) tulong)) E0 le mf Out_normal.
Proof.
  intros HB HM HC HCount HLen HS.
  eapply exec_Sassign_value with (v := Vlong (sha256_read_counter count len))
    (v2 := Vlong (sha256_read_counter count len))
    (b := bc) (ofs := Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)).
  - apply eval_sha256_context_field_lvalue; exact HC.
  - eapply eval_Ebinop with
      (v1 := Vlong (Int64.shl (Int64.mul count (Int64.repr 1)) (Int64.repr 6))) (v2 := Vlong len).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.mul count (Int64.repr 1))) (v2 := Vint (Int.repr 6)).
      * eapply eval_Ebinop with (v1 := Vlong count) (v2 := Vint (Int.repr 1));
          [apply eval_Etempvar; exact HCount|apply eval_Econst_int|reflexivity].
      * apply eval_Econst_int.
      * reflexivity.
    + apply eval_Etempvar; exact HLen.
    + reflexivity.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.storev. change (Mem.store Mint64 m bc
      (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset CtxCounter))))
      (Vlong (sha256_read_counter count len)) = Some mf).
    rewrite sha256_context_address by assumption; exact HS.
Qed.

Theorem exec_sha256_read_counter_from_observation e le m bc base bl count len :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  e!_len = Some (bl, tulong) -> Mem.load Mint64 m bl 0 = Some (Vlong len) ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  Mem.valid_access m Mint64 bc (base + 8) Writable ->
  exists mf lef,
    Clight2.exec_stmt ge0 e le m sha256_read_counter_stmt E0 lef mf Out_normal /\
    Mem.store Mint64 m bc (base + 8) (Vlong (sha256_read_counter count len)) = Some mf /\
    Mem.load Mint64 mf bc (base + 8) = Some (Vlong (sha256_read_counter count len)).
Proof.
  intros HB HM HE HL HC HCount HW.
  destruct (Mem.valid_access_store m Mint64 bc (base + 8)
    (Vlong (sha256_read_counter count len)) HW) as [mf HS].
  set (lef := PTree.set _t'5 (Vlong len) le).
  exists mf, lef. split.
  - unfold sha256_read_counter_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lef) (m1 := m).
    + apply exec_set. eapply eval_Elvalue.
      * apply eval_Evar_local; exact HE.
      * apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
    + eapply exec_sha256_read_counter_store; [exact HB|exact HM|
        unfold lef; rewrite PTree.gso by discriminate; exact HC|
        unfold lef; rewrite PTree.gso by discriminate; exact HCount|
        unfold lef; apply PTree.gss|exact HS].
  - split; [exact HS|]. rewrite (Mem.load_store_same _ _ _ _ _ _ HS); reflexivity.
Qed.

Theorem exec_sha256_read_counter_from_memory e le m bc base bl count len :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  e!_len = Some (bl, tulong) -> Mem.load Mint64 m bl 0 = Some (Vlong len) ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  Mem.valid_access m Mint64 bc (base + 8) Writable -> sha256_max_counter_at m ->
  exists mf lef,
    Clight2.exec_stmt ge0 e le m sha256_read_counter_stmt E0 lef mf Out_normal /\
    Mem.store Mint64 m bc (base + 8) (Vlong (sha256_read_counter count len)) = Some mf /\
    Mem.load Mint64 mf bc (base + 8) = Some (Vlong (sha256_read_counter count len)) /\
    sha256_max_counter_at mf.
Proof.
  intros HB HM HE HL HC HCount HW HGlobal.
  destruct (exec_sha256_read_counter_from_observation e le m bc base bl count len
    HB HM HE HL HC HCount HW) as (mf & lef & HExec & HS & HCounter).
  exists mf, lef. split; [exact HExec|]. split; [exact HS|]. split; [exact HCounter|].
  eapply sha256_max_counter_store; eauto.
Qed.

(** Field observations for the actual pinned LP64 sha256_context layout.
    The block follows the counter, not the reverse. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive sha256_context_slot := CtxOutput | CtxCounter | CtxBlock | CtxOverflow.
Definition sha256_context_field k := match k with
  | CtxOutput => _output | CtxCounter => _counter | CtxBlock => _block | CtxOverflow => _overflow end.
Definition sha256_context_offset k : Z := match k with
  | CtxOutput => 0 | CtxCounter => 8 | CtxBlock => 16 | CtxOverflow => 80 end.
Definition sha256_context_field_type k := match k with
  | CtxOutput => tptr tuint | CtxCounter => tulong | CtxBlock => tarray tuchar 64 | CtxOverflow => tbool end.
Definition sha256_context_field_expr k id := Efield
  (Ederef (Etempvar id (tptr (Tstruct _sha256_context noattr))) (Tstruct _sha256_context noattr))
  (sha256_context_field k) (sha256_context_field_type k).

Lemma sha256_context_size : sizeof ge0 (Tstruct _sha256_context noattr) = 88.
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_context_address base k : 0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset k))) =
    base + sha256_context_offset k.
Proof.
  intros HB HM. assert (HD : 0 <= sha256_context_offset k <= 80) by (destruct k; cbn; lia).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr base) by lia.
  rewrite (Ptrofs.unsigned_repr (sha256_context_offset k)) by lia.
  apply Ptrofs.unsigned_repr; lia.
Qed.
Lemma eval_sha256_context_field_lvalue k id e le m bc base :
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_lvalue ge0 e le m (sha256_context_field_expr k id)
    bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset k))) Full.
Proof.
  intros HP. eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_Etempvar; exact HP.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
  - destruct k; vm_compute; reflexivity.
Qed.
Lemma eval_sha256_context_field k id e le m bc base chunk v :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  access_mode (sha256_context_field_type k) = By_value chunk ->
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  Mem.load chunk m bc (base + sha256_context_offset k) = Some v ->
  eval_expr ge0 e le m (sha256_context_field_expr k id) v.
Proof.
  intros HB HM HK HP HL. eapply eval_Elvalue.
  - apply eval_sha256_context_field_lvalue; exact HP.
  - apply deref_loc_value with (chunk := chunk); [exact HK|].
    unfold Mem.loadv. rewrite sha256_context_address by assumption; exact HL.
Qed.
Lemma eval_sha256_context_block id e le m bc base :
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_expr ge0 e le m (sha256_context_field_expr CtxBlock id)
    (Vptr bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 16))).
Proof.
  intros HP. eapply eval_Elvalue; [apply eval_sha256_context_field_lvalue; exact HP|].
  apply deref_loc_reference; reflexivity.
Qed.

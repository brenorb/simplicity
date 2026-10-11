(** Actual whole-struct self-copy, at the real 88-byte affine size. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp C.jet_secp_self_copy_assign.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition affine_negate_copy_stmt : statement :=
  Sassign (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr))) (Tstruct __6121 noattr))
    (Ederef (Etempvar _a (tptr (Tstruct __6121 noattr))) (Tstruct __6121 noattr)).

Theorem exec_affine_negate_self_copy_owned le m b :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  le!_a = Some (Vptr b Ptrofs.zero) ->
  Mem.range_perm m b 0 88 Cur Freeable ->
  exists mf,
    Clight2.exec_stmt secp_ge empty_env le m affine_negate_copy_stmt E0 le mf Out_normal /\
    Mem.unchanged_on (fun _ _ => True) m mf /\
    Mem.range_perm mf b 0 88 Cur Freeable.
Proof.
  intros HR HA HP.
  assert (HAlign : sizeof secp_ge (Tstruct __6121 noattr) > 0 ->
    (alignof_blockcopy secp_ge (Tstruct __6121 noattr) | Ptrofs.unsigned Ptrofs.zero)).
  { intros _; change (8 | 0); exists 0; reflexivity. }
  assert (HW : Mem.range_perm m b (Ptrofs.unsigned Ptrofs.zero)
    (Ptrofs.unsigned Ptrofs.zero + sizeof secp_ge (Tstruct __6121 noattr)) Cur Writable).
  { change (Mem.range_perm m b 0 88 Cur Writable).
    intros pos HPos; eapply Mem.perm_implies; [apply HP;exact HPos|constructor]. }
  destruct (assign_loc_owned_self_copy secp_ge (Tstruct __6121 noattr) m b Ptrofs.zero
    eq_refl ltac:(change (0 <= 88);lia) HAlign HW) as (mf & HAssign & HF).
  exists mf; split.
  - unfold affine_negate_copy_stmt.
    eapply exec_Sassign_copy with (b := b) (b' := b) (ofs := Ptrofs.zero)
      (ofs' := Ptrofs.zero) (v := Vptr b Ptrofs.zero).
    + apply eval_Ederef; apply eval_Etempvar; exact HR.
    + eapply eval_Elvalue.
      * apply eval_Ederef; apply eval_Etempvar; exact HA.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HAssign.
  - split; [exact HF|].
    intros pos HPos; eapply Mem.perm_unchanged_on;
      [exact HF|exact I|apply HP;exact HPos].
Qed.
Print Assumptions exec_affine_negate_self_copy_owned.

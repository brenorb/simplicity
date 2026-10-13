(** Shared actual affine field layout/lvalues for original reader and writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp C.jet_secp_affine_y_tail.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma affine_field_layout fid delta :
  In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] ->
  exists co, (genv_cenv secp_ge)!__6121 = Some co /\
    field_offset secp_ge fid (co_members co) = Errors.OK (delta,Full).
Proof.
  intro H; pose proof affine_field_members as HM.
  destruct ((genv_cenv secp_ge)!__6121) as [co|] eqn:HC; [|discriminate].
  exists co; split; [reflexivity|]. inversion HM as [HMembers]; rewrite HMembers.
  destruct H as [H|[H|[H|H]]]; [| | |contradiction];
    inversion H; subst; vm_compute; reflexivity.
Qed.

Lemma eval_affine_pointer_field le m b base pid fid delta ty :
  In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] ->
  0 <= base -> base+88 <= Ptrofs.max_unsigned ->
  le!pid = Some (Vptr b (Ptrofs.repr base)) ->
  eval_lvalue secp_ge empty_env le m
    (Efield (Ederef (Etempvar pid (tptr (Tstruct __6121 noattr)))
      (Tstruct __6121 noattr)) fid ty) b (Ptrofs.repr (base+delta)) Full.
Proof.
  intros HF HB HM HP.
  assert (HD : 0 <= delta <= 80).
  { destruct HF as [H|[H|[H|H]]]; [| | |contradiction]; inversion H; lia. }
  destruct (affine_field_layout fid delta HF) as (co & HC & HO).
  replace (Ptrofs.repr (base+delta)) with
    (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr delta)).
  - eapply eval_Efield_struct with (co := co) (delta := delta).
    + eapply eval_Elvalue.
      * apply eval_Ederef; apply eval_Etempvar; exact HP.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HC.
    + exact HO.
  - unfold Ptrofs.add; rewrite !Ptrofs.unsigned_repr by lia; reflexivity.
Qed.

Lemma eval_affine_field_address le m b base pid fid delta :
  In (fid,delta) [(_x,0);(_y,40)] ->
  0 <= base -> base+88 <= Ptrofs.max_unsigned ->
  le!pid = Some (Vptr b (Ptrofs.repr base)) ->
  eval_expr secp_ge empty_env le m
    (Eaddrof (Efield (Ederef (Etempvar pid (tptr (Tstruct __6121 noattr)))
      (Tstruct __6121 noattr)) fid (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr)))
    (Vptr b (Ptrofs.repr (base+delta))).
Proof.
  intros HF HB HM HP; apply eval_Eaddrof; apply eval_affine_pointer_field; try assumption.
  destruct HF as [H|[H|H]]; [left|right;left|contradiction]; exact H.
Qed.

(** Actual X/Y/Z by-copy assignments in original in-place point negation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_gej_infinity_layout C.jet_secp_self_copy_assign.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma eval_gej_pointer_field le m b base pid fid delta ty :
  In (fid, delta) [(_x,0); (_y,40); (_z,80); (_infinity,120)] ->
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!pid = Some (Vptr b (Ptrofs.repr base)) ->
  eval_lvalue secp_ge empty_env le m
    (Efield (Ederef (Etempvar pid (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) fid ty)
    b (Ptrofs.repr (base + delta)) Full.
Proof.
  intros HF HB HM HP.
  assert (HD : 0 <= delta <= 120).
  { destruct HF as [H|[H|[H|[H|H]]]]; [| | | |contradiction];
      inversion H; lia. }
  destruct (gej_infinity_field_layout fid delta HF) as [co [HC HO]].
  replace (Ptrofs.repr (base + delta)) with
    (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr delta)).
  - eapply eval_Efield_struct with (co := co) (delta := delta).
    + eapply eval_Elvalue.
      * apply eval_Ederef. apply eval_Etempvar; exact HP.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HC.
    + exact HO.
  - unfold Ptrofs.add. rewrite !Ptrofs.unsigned_repr by lia. reflexivity.
Qed.

Definition gej_negate_field_copy_stmt fid : statement :=
  Sassign
    (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) fid (Tstruct __5467 noattr))
    (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) fid (Tstruct __5467 noattr)).

Lemma exec_gej_negate_self_field_owned le m b base fid delta :
  In (fid, delta) [(_x,0); (_y,40); (_z,80)] ->
  0 <= base -> (8 | base) -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  Mem.range_perm m b base (base + 128) Cur Freeable ->
  exists mf,
    Clight2.exec_stmt secp_ge empty_env le m
      (gej_negate_field_copy_stmt fid) E0 le mf Out_normal /\
    Mem.unchanged_on (fun _ _ => True) m mf /\
    Mem.range_perm mf b base (base + 128) Cur Freeable.
Proof.
  intros HF HB HA HM HR HS HP.
  assert (HD : 0 <= delta /\ delta+40 <= 128 /\ (8 | delta)).
  { destruct HF as [H|[H|[H|H]]]; [| | |contradiction];
      inversion H; subst; repeat split; try lia;
      [exists 0|exists 5|exists 10]; reflexivity. }
  destruct HD as [HD [HL HDiv]].
  assert (HField : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]).
  { destruct HF as [H|[H|[H|H]]];
      [left|right;left|right;right;left|contradiction]; exact H. }
  assert (HU : Ptrofs.unsigned (Ptrofs.repr (base+delta)) = base+delta).
  { apply Ptrofs.unsigned_repr; lia. }
  assert (HAlign : sizeof secp_ge (Tstruct __5467 noattr) > 0 ->
      (alignof_blockcopy secp_ge (Tstruct __5467 noattr) |
        Ptrofs.unsigned (Ptrofs.repr (base+delta)))).
  { intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr (base+delta))).
    rewrite HU. destruct HA as [k HK]; destruct HDiv as [d HDeltaEq].
    exists (k+d); lia. }
  assert (HWritable : Mem.range_perm m b
      (Ptrofs.unsigned (Ptrofs.repr (base+delta)))
      (Ptrofs.unsigned (Ptrofs.repr (base+delta)) +
        sizeof secp_ge (Tstruct __5467 noattr)) Cur Writable).
  { rewrite HU. change (sizeof secp_ge (Tstruct __5467 noattr)) with 40.
    intros pos HPos. eapply Mem.perm_implies; [apply HP;lia|constructor]. }
  destruct (assign_loc_owned_self_copy secp_ge (Tstruct __5467 noattr)
    m b (Ptrofs.repr (base+delta)) eq_refl ltac:(change (0 <= 40);lia)
    HAlign HWritable) as (mf & HAssign & HFrame).
  exists mf; split.
  - unfold gej_negate_field_copy_stmt.
    eapply exec_Sassign_copy with (b := b) (b' := b)
      (ofs := Ptrofs.repr (base+delta)) (ofs' := Ptrofs.repr (base+delta))
      (v := Vptr b (Ptrofs.repr (base+delta))).
    + exact (eval_gej_pointer_field le m b base _r fid delta
        (Tstruct __5467 noattr) HField HB HM HR).
    + eapply eval_Elvalue.
      * exact (eval_gej_pointer_field le m b base _a fid delta
          (Tstruct __5467 noattr) HField HB HM HS).
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HAssign.
  - split; [exact HFrame|].
    intros pos HPos. eapply Mem.perm_unchanged_on; [exact HFrame|exact I|apply HP;exact HPos].
Qed.
Print Assumptions exec_gej_negate_self_field_owned.

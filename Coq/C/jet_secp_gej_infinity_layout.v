(** Exact generated point layout and flag assignment for the original initializer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events ClightBigstep.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma gej_infinity_field_offset fid delta :
  In (fid, delta) [(_x,0); (_y,40); (_z,80); (_infinity,120)] ->
  option_map (fun co => field_offset secp_ge fid (co_members co))
    ((genv_cenv secp_ge)!__6123) = Some (Errors.OK (delta, Full)).
Proof.
  intros [H|[H|[H|[H|H]]]]; [| | | |contradiction];
    inversion H; subst; vm_compute; reflexivity.
Qed.

Lemma gej_infinity_members :
  option_map co_members ((genv_cenv secp_ge)!__6123) =
  Some [Member_plain _x (Tstruct __5467 noattr);
        Member_plain _y (Tstruct __5467 noattr);
        Member_plain _z (Tstruct __5467 noattr);
        Member_plain _infinity tint].
Proof. vm_compute; reflexivity. Qed.

Lemma gej_infinity_field_layout fid delta :
  In (fid, delta) [(_x,0); (_y,40); (_z,80); (_infinity,120)] ->
  exists co, (genv_cenv secp_ge)!__6123 = Some co /\
    field_offset secp_ge fid (co_members co) = Errors.OK (delta, Full).
Proof.
  intro H. pose proof gej_infinity_members as HM.
  destruct ((genv_cenv secp_ge)!__6123) as [co|] eqn:HC; [|discriminate].
  exists co; split; [reflexivity|].
  inversion HM as [HMembers]. rewrite HMembers.
  destruct H as [H|[H|[H|[H|H]]]]; [| | | |contradiction];
    inversion H; subst; vm_compute; reflexivity.
Qed.

Lemma eval_gej_infinity_field le m b base fid delta ty :
  In (fid, delta) [(_x,0); (_y,40); (_z,80); (_infinity,120)] ->
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  eval_lvalue secp_ge empty_env le m
    (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) fid ty)
    b (Ptrofs.repr (base + delta)) Full.
Proof.
  intros HF HB HM HR.
  assert (HD : 0 <= delta <= 120).
  { destruct HF as [H|[H|[H|[H|H]]]]; [| | | |contradiction];
      inversion H; lia. }
  destruct (gej_infinity_field_layout fid delta HF) as [co [HC HO]].
  replace (Ptrofs.repr (base + delta)) with
    (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr delta)).
  - eapply eval_Efield_struct with (co := co) (delta := delta).
    + eapply eval_Elvalue.
      * apply eval_Ederef. apply eval_Etempvar; exact HR.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HC.
    + exact HO.
  - unfold Ptrofs.add. rewrite !Ptrofs.unsigned_repr by lia. reflexivity.
Qed.

Lemma eval_gej_infinity_field_address le m b base fid delta :
  In (fid, delta) [(_x,0); (_y,40); (_z,80)] ->
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  eval_expr secp_ge empty_env le m
    (Eaddrof
      (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
        (Tstruct __6123 noattr)) fid (Tstruct __5467 noattr))
      (tptr (Tstruct __5467 noattr)))
    (Vptr b (Ptrofs.repr (base + delta))).
Proof.
  intros HF HB HM HR. apply eval_Eaddrof.
  apply eval_gej_infinity_field; try assumption.
  destruct HF as [H|[H|[H|H]]]; [left|right;left|right;right;left|contradiction]; exact H.
Qed.

Lemma exec_gej_infinity_flag le m mi b base :
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  Mem.store Mint32 m b (base + 120) (Vint Int.one) = Some mi ->
  Clight2.exec_stmt secp_ge empty_env le m
    (Sassign
      (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
        (Tstruct __6123 noattr)) _infinity tint)
      (Econst_int (Int.repr 1) tint)) E0 le mi Out_normal.
Proof.
  intros HB HM HR HS.
  eapply exec_Sassign with (loc := b) (ofs := Ptrofs.repr (base + 120))
    (bf := Full) (v2 := Vint Int.one) (v := Vint Int.one).
  - apply eval_gej_infinity_field; [right;right;right;left;reflexivity|assumption|assumption|assumption].
  - apply eval_Econst_int.
  - reflexivity.
  - eapply assign_loc_value with (chunk := Mint32); [reflexivity|].
    unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

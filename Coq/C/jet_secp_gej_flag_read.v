(** Original point flag accessor; exact memory is unchanged. Internal support only. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events ClightBigstep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_infinity_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_flag_env b base : temp_env :=
  PTree.set _a (Vptr b (Ptrofs.repr base))
    (create_undef_temps (fn_temps f_secp256k1_gej_is_infinity)).

Lemma gej_flag_entry m b base :
  function_entry2 secp_ge f_secp256k1_gej_is_infinity
    [Vptr b (Ptrofs.repr base)] m empty_env (gej_flag_env b base) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros x y HX HY HE; cbn in HX, HY.
    destruct HX as [HX|HX]; [|contradiction].
    destruct HY as [HY|HY]; [|contradiction].
    subst x y; discriminate.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_gej_flag_load m le b base flag :
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  Mem.load Mint32 m b (base + 120) = Some (Vint flag) ->
  eval_expr secp_ge empty_env le m
    (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) _infinity tint) (Vint flag).
Proof.
  intros HB HM HA HL.
  destruct (gej_infinity_field_layout _infinity 120
    ltac:(right; right; right; left; reflexivity)) as [co [HC HO]].
  eapply eval_Elvalue with (loc := b) (ofs := Ptrofs.repr (base + 120)) (bf := Full).
  - replace (Ptrofs.repr (base + 120)) with
      (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 120)).
    + eapply eval_Efield_struct with (co := co) (delta := 120).
      * eapply eval_Elvalue.
        -- apply eval_Ederef. apply eval_Etempvar; exact HA.
        -- apply deref_loc_copy; reflexivity.
      * reflexivity.
      * exact HC.
      * exact HO.
    + unfold Ptrofs.add. rewrite !Ptrofs.unsigned_repr by lia. reflexivity.
  - eapply deref_loc_value with (chunk := Mint32).
    + reflexivity.
    + unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

Theorem eval_gej_flag_accessor m b base flag :
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m b (base + 120) = Some (Vint flag) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_is_infinity)
    [Vptr b (Ptrofs.repr base)] E0 m (Vint flag).
Proof.
  intros HB HM HL.
  eapply eval_funcall_internal with (e := empty_env)
    (le1 := gej_flag_env b base)
    (le2 := PTree.set _t'1 (Vint flag) (gej_flag_env b base))
    (m1 := m) (m2 := m) (out := Out_return (Some (Vint flag, tint))).
  - apply gej_flag_entry.
  - change (Clight2.exec_stmt secp_ge empty_env (gej_flag_env b base) m
      (Ssequence
        (Sset _t'1 (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
          (Tstruct __6123 noattr)) _infinity tint))
        (Sreturn (Some (Etempvar _t'1 tint)))) E0
      (PTree.set _t'1 (Vint flag) (gej_flag_env b base)) m
      (Out_return (Some (Vint flag, tint)))).
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'1 (Vint flag) (gej_flag_env b base)).
    + apply exec_Sset. eapply eval_gej_flag_load; try eassumption.
      unfold gej_flag_env; apply PTree.gss.
    + apply exec_Sreturn_some. apply eval_Etempvar; apply PTree.gss.
  - split; [discriminate|reflexivity].
  - reflexivity.
Qed.
Print Assumptions eval_gej_flag_accessor.

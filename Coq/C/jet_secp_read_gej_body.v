(** Exact original read_gej call tree. Intermediate calls are discharged by
    the owned-memory composition, not used as public jet preconditions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_body C.jet_secp_public_copy.
Require Import C.jet_secp_zero_body C.jet_secp_gej_infinity_layout C.jet_secp_gej_read_flag_store.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition read_gej_field_stmt fid : statement :=
  Scall None (Evar _read_fe (Tfunction
    (Tcons (tptr (Tstruct __5467 noattr))
      (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)) tvoid cc_default))
    [Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
       (Tstruct __6123 noattr)) fid (Tstruct __5467 noattr))
       (tptr (Tstruct __5467 noattr));
     Etempvar _src (tptr (Tstruct _frameItem noattr))].
Definition read_gej_zero_stmt : statement :=
  Scall (Some _t'1) (Evar _secp256k1_fe_is_zero (Tfunction
    (Tcons (tptr (Tstruct __5467 noattr)) Tnil) tint cc_default))
    [Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
       (Tstruct __6123 noattr)) _z (Tstruct __5467 noattr))
       (tptr (Tstruct __5467 noattr))].
Definition read_gej_flag_stmt : statement :=
  Sassign (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
    (Tstruct __6123 noattr)) _infinity tint) (Etempvar _t'1 tint).
Lemma read_gej_body : fn_body f_read_gej =
  Ssequence (read_gej_field_stmt _x)
    (Ssequence (read_gej_field_stmt _y)
      (Ssequence (read_gej_field_stmt _z)
        (Ssequence read_gej_zero_stmt read_gej_flag_stmt))).
Proof. reflexivity. Qed.

Lemma exec_read_gej_field le m mf b bl fid delta :
  In (fid,delta) [(_x,0);(_y,40);(_z,80)] ->
  le!_r = Some (Vptr b (Ptrofs.repr 0)) ->
  le!_src = Some (Vptr bl Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr b (Ptrofs.repr delta); Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m (read_gej_field_stmt fid) E0 le mf Out_normal.
Proof.
  intros HF HR HS HC.
  destruct secp_public_helper_symbols as (HRS & HRF & HWS & HWF).
  unfold read_gej_field_stmt.
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _read_fe) Ptrofs.zero)
    (vargs := [Vptr b (Ptrofs.repr delta); Vptr bl Ptrofs.zero])
    (f := Internal f_read_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HRS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + exact (eval_gej_infinity_field_address le m b 0 fid delta HF
        ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HR).
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar; exact HS.
      * reflexivity.
      * apply eval_Enil.
  - exact HRF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_read_gej_zero le m mf b flag :
  le!_r = Some (Vptr b (Ptrofs.repr 0)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
    [Vptr b (Ptrofs.repr 80)] E0 mf (Vint flag) ->
  Clight2.exec_stmt secp_ge empty_env le m read_gej_zero_stmt E0
    (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
  intros HR HC; destruct secp_zero_helper_symbols as [HZS HZF].
  unfold read_gej_zero_stmt.
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _secp256k1_fe_is_zero) Ptrofs.zero)
    (vargs := [Vptr b (Ptrofs.repr 80)])
    (f := Internal f_secp256k1_fe_is_zero) (vres := Vint flag).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HZS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + exact (eval_gej_infinity_field_address le m b 0 _z 80
        ltac:(right;right;left;reflexivity) ltac:(lia)
        ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HR).
    + reflexivity.
    + apply eval_Enil.
  - exact HZF.
  - reflexivity.
  - exact HC.
Qed.

Definition read_gej_env b bl : temp_env :=
  PTree.set _src (Vptr bl Ptrofs.zero)
    (PTree.set _r (Vptr b (Ptrofs.repr 0)) (create_undef_temps (fn_temps f_read_gej))).
Lemma read_gej_entry m b bl :
  function_entry2 secp_ge f_read_gej [Vptr b (Ptrofs.repr 0);Vptr bl Ptrofs.zero]
    m empty_env (read_gej_env b bl) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros x y HX HY HE; cbn in HX, HY.
    destruct HY as [HY|HY]; [|contradiction].
    subst y. destruct HX as [HX|[HX|HX]]; [| |contradiction];
      subst x; discriminate.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_read_gej_from_calls m mx my mz mt mf b bl flag :
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr b (Ptrofs.repr 0);Vptr bl Ptrofs.zero] E0 mx Vundef ->
  Clight2.eval_funcall secp_ge mx (Internal f_read_fe)
    [Vptr b (Ptrofs.repr 40);Vptr bl Ptrofs.zero] E0 my Vundef ->
  Clight2.eval_funcall secp_ge my (Internal f_read_fe)
    [Vptr b (Ptrofs.repr 80);Vptr bl Ptrofs.zero] E0 mz Vundef ->
  Clight2.eval_funcall secp_ge mz (Internal f_secp256k1_fe_is_zero)
    [Vptr b (Ptrofs.repr 80)] E0 mt (Vint flag) ->
  Clight2.exec_stmt secp_ge empty_env
    (PTree.set _t'1 (Vint flag) (read_gej_env b bl)) mt read_gej_flag_stmt E0
    (PTree.set _t'1 (Vint flag) (read_gej_env b bl)) mf Out_normal ->
  Clight2.eval_funcall secp_ge m (Internal f_read_gej)
    [Vptr b (Ptrofs.repr 0);Vptr bl Ptrofs.zero] E0 mf Vundef.
Proof.
  intros HX HY HZ HT HF.
  assert (HR : (read_gej_env b bl)!_r = Some (Vptr b (Ptrofs.repr 0))).
  { unfold read_gej_env; rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HS : (read_gej_env b bl)!_src = Some (Vptr bl Ptrofs.zero)).
  { unfold read_gej_env; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := read_gej_env b bl)
    (le2 := PTree.set _t'1 (Vint flag) (read_gej_env b bl))
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply read_gej_entry.
  - rewrite read_gej_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mx) (le1 := read_gej_env b bl).
    + eapply exec_read_gej_field; [left;reflexivity|exact HR|exact HS|exact HX].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := my) (le1 := read_gej_env b bl).
      * eapply exec_read_gej_field; [right;left;reflexivity|exact HR|exact HS|exact HY].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mz) (le1 := read_gej_env b bl).
        -- eapply exec_read_gej_field; [right;right;left;reflexivity|exact HR|exact HS|exact HZ].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mt)
             (le1 := PTree.set _t'1 (Vint flag) (read_gej_env b bl)).
           ++ eapply exec_read_gej_zero; eassumption.
           ++ exact HF.
  - reflexivity.
  - reflexivity.
Qed.
Print Assumptions eval_read_gej_from_calls.

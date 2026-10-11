(** The actual affine writer entry, two generated calls, return and local free. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_body C.jet_secp_public_copy.
Require Import C.jet_secp_affine_fields.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition write_ge_field_stmt fid : statement :=
  Scall None (Evar _write_fe (Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct __5467 noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr)))
       (Tstruct __6121 noattr)) fid (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr))].
Lemma write_ge_body : fn_body f_write_ge =
  Ssequence (write_ge_field_stmt _x) (write_ge_field_stmt _y).
Proof. reflexivity. Qed.

Lemma exec_write_ge_field le m mf b bd dbase fid delta :
  In (fid,delta) [(_x,0);(_y,40)] ->
  le!_r = Some (Vptr b (Ptrofs.repr 0)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr delta)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m (write_ge_field_stmt fid) E0 le mf Out_normal.
Proof.
  intros HF HR HD HC; destruct secp_public_helper_symbols as (HRS & HRF & HWS & HWF).
  unfold write_ge_field_stmt.
  eapply exec_Scall with (vf := Vptr (secp_symbol_block _write_fe) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr delta)])
    (f := Internal f_write_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HWS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar;exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * exact (eval_affine_field_address le m b 0 _r fid delta HF ltac:(lia)
          ltac:(change (88 <= 18446744073709551615);lia) HR).
      * reflexivity.
      * apply eval_Enil.
  - exact HWF.
  - reflexivity.
  - exact HC.
Qed.

Definition write_ge_env b bd dbase : temp_env :=
  PTree.set _r (Vptr b (Ptrofs.repr 0))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps (fn_temps f_write_ge))).
Lemma write_ge_entry m b bd dbase :
  function_entry2 secp_ge f_write_ge [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)]
    m empty_env (write_ge_env b bd dbase) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor;cbn;intuition discriminate.
  - intros x y HX HY HE;cbn in HX,HY;contradiction.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_write_ge_from_calls m mx mf b bd dbase :
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mx Vundef ->
  Clight2.eval_funcall secp_ge mx (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 40)] E0 mf Vundef ->
  Clight2.eval_funcall secp_ge m (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef.
Proof.
  intros HX HY.
  assert (HR : (write_ge_env b bd dbase)!_r = Some (Vptr b (Ptrofs.repr 0)))
    by (unfold write_ge_env;apply PTree.gss).
  assert (HD : (write_ge_env b bd dbase)!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold write_ge_env;rewrite PTree.gso by discriminate;apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := write_ge_env b bd dbase)
    (le2 := write_ge_env b bd dbase) (m1 := m) (m2 := mf) (out := Out_normal).
  - apply write_ge_entry.
  - rewrite write_ge_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mx) (le1 := write_ge_env b bd dbase).
    + eapply exec_write_ge_field;[left;reflexivity|exact HR|exact HD|exact HX].
    + eapply exec_write_ge_field;[right;left;reflexivity|exact HR|exact HD|exact HY].
  - reflexivity.
  - reflexivity.
Qed.
Print Assumptions eval_write_ge_from_calls.

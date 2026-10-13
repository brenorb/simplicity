(** Actual original affine reader call tree; final contracts discharge calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_body C.jet_secp_public_copy.
Require Import C.jet_secp_affine_fields C.jet_secp_affine_read_flag.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition read_ge_field_stmt fid : statement :=
  Scall None (Evar _read_fe (Tfunction
    (Tcons (tptr (Tstruct __5467 noattr))
      (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)) tvoid cc_default))
    [Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr)))
       (Tstruct __6121 noattr)) fid (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));
     Etempvar _src (tptr (Tstruct _frameItem noattr))].
Lemma read_ge_body : fn_body f_read_ge =
  Ssequence (read_ge_field_stmt _x) (Ssequence (read_ge_field_stmt _y) affine_read_flag_stmt).
Proof. reflexivity. Qed.

Lemma exec_read_ge_field le m mf b bl fid delta :
  In (fid,delta) [(_x,0);(_y,40)] ->
  le!_r = Some (Vptr b Ptrofs.zero) -> le!_src = Some (Vptr bl Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr b (Ptrofs.repr delta);Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m (read_ge_field_stmt fid) E0 le mf Out_normal.
Proof.
  intros HF HR HS HC; destruct secp_public_helper_symbols as (HRS & HRF & HWS & HWF).
  unfold read_ge_field_stmt.
  eapply exec_Scall with (vf := Vptr (secp_symbol_block _read_fe) Ptrofs.zero)
    (vargs := [Vptr b (Ptrofs.repr delta);Vptr bl Ptrofs.zero]) (f := Internal f_read_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HRS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + exact (eval_affine_field_address le m b 0 _r fid delta HF ltac:(lia)
        ltac:(change (88 <= 18446744073709551615);lia) HR).
    + reflexivity.
    + eapply eval_Econs; [apply eval_Etempvar;exact HS|reflexivity|apply eval_Enil].
  - exact HRF.
  - reflexivity.
  - exact HC.
Qed.

Definition read_ge_env b bl : temp_env :=
  PTree.set _src (Vptr bl Ptrofs.zero)
    (PTree.set _r (Vptr b Ptrofs.zero) (create_undef_temps (fn_temps f_read_ge))).
Lemma read_ge_entry m b bl :
  function_entry2 secp_ge f_read_ge [Vptr b Ptrofs.zero;Vptr bl Ptrofs.zero]
    m empty_env (read_ge_env b bl) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY HE; cbn in HX,HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in HE;discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.

Lemma eval_read_ge_from_calls m mx my mf b bl :
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr b Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mx Vundef ->
  Clight2.eval_funcall secp_ge mx (Internal f_read_fe)
    [Vptr b (Ptrofs.repr 40);Vptr bl Ptrofs.zero] E0 my Vundef ->
  Clight2.exec_stmt secp_ge empty_env (read_ge_env b bl) my affine_read_flag_stmt E0
    (read_ge_env b bl) mf Out_normal ->
  Clight2.eval_funcall secp_ge m (Internal f_read_ge)
    [Vptr b Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef.
Proof.
  intros HX HY HF.
  assert (HR : (read_ge_env b bl)!_r = Some (Vptr b Ptrofs.zero)).
  { unfold read_ge_env; rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HS : (read_ge_env b bl)!_src = Some (Vptr bl Ptrofs.zero)).
  { unfold read_ge_env; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := read_ge_env b bl)
    (le2 := read_ge_env b bl) (m1 := m) (m2 := mf) (out := Out_normal).
  - apply read_ge_entry.
  - rewrite read_ge_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mx) (le1 := read_ge_env b bl).
    + eapply exec_read_ge_field; [left;reflexivity|exact HR|exact HS|exact HX].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := my) (le1 := read_ge_env b bl).
      * eapply exec_read_ge_field; [right;left;reflexivity|exact HR|exact HS|exact HY].
      * exact HF.
  - reflexivity.
  - reflexivity.
Qed.
Print Assumptions eval_read_ge_from_calls.

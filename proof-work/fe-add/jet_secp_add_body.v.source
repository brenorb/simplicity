(** Exact original three-local field-add statements and compositional calls. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_public_copy C.jet_secp_public_body.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_public_add_env bl ba bb : env :=
  PTree.set jets_secp._b (bb, secp_field_type) (secp_public_env bl ba).
Definition secp_read_field_stmt (id : ident) : statement :=
  Scall None
    (Evar jets_secp._read_fe (Tfunction
      (Tcons (tptr secp_field_type) (Tcons (tptr secp_frame_type) Tnil)) tvoid cc_default))
    [Eaddrof (Evar id secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._src secp_frame_type) (tptr secp_frame_type)].
Definition secp_public_add_stmt : statement :=
  Scall None
    (Evar jets_secp._secp256k1_fe_add (Tfunction
      (Tcons (tptr secp_field_type) (Tcons (tptr secp_field_type) Tnil)) tvoid cc_default))
    [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type)].
Definition secp_fe_add_rest : statement :=
  Ssequence (secp_read_field_stmt jets_secp._a)
    (Ssequence (secp_read_field_stmt jets_secp._b)
      (Ssequence secp_public_add_stmt
        (Ssequence secp_public_write_stmt
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))))).
Lemma secp_fe_add_body :
  fn_body f_simplicity_fe_add =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) secp_fe_add_rest.
Proof. reflexivity. Qed.
Lemma secp_add_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._secp256k1_fe_add =
    Some (secp_symbol_block jets_secp._secp256k1_fe_add) /\
  Genv.find_funct secp_ge
    (Vptr (secp_symbol_block jets_secp._secp256k1_fe_add) Ptrofs.zero) =
    Some (Internal f_secp256k1_fe_add).
Proof. vm_compute; split; reflexivity. Qed.

Lemma exec_secp_read_field e le m mf id ba bl :
  e!jets_secp._read_fe = None ->
  e!id = Some (ba, secp_field_type) ->
  e!jets_secp._src = Some (bl, secp_frame_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (secp_read_field_stmt id) E0 le mf Out_normal.
Proof.
  intros HGlobal HField HSource HCall.
  destruct secp_public_helper_symbols as (HRS & HRF & HWS & HWF).
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._read_fe) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero])
    (f := Internal f_read_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [exact HGlobal|exact HRS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; exact HField.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; exact HSource.
      * reflexivity.
      * apply eval_Enil.
  - exact HRF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_secp_add_fields le m mf bl ba bb :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_add_env bl ba bb) le m
    secp_public_add_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct secp_add_helper_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._secp256k1_fe_add) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero])
    (f := Internal f_secp256k1_fe_add) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_secp_write_field e le m mf ba bd dbase :
  e!jets_secp._write_fe = None -> e!jets_secp._a = Some (ba, secp_field_type) ->
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m secp_public_write_stmt E0 le mf Out_normal.
Proof.
  intros HGlobal HField HDst HCall.
  destruct secp_public_helper_symbols as (HRS & HRF & HWS & HWF).
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._write_fe) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero])
    (f := Internal f_write_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [exact HGlobal|exact HWS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HDst.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; exact HField.
      * reflexivity.
      * apply eval_Enil.
  - exact HWF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_secp_add_rest_calls le m ma mb mn mf bl ba bb bd dbase :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef ->
  Clight2.eval_funcall secp_ge ma (Internal f_read_fe)
    [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mb Vundef ->
  Clight2.eval_funcall secp_ge mb (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_add_env bl ba bb) le m secp_fe_add_rest E0 le mf
    (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HDst HA HB HAdd HWrite. unfold secp_fe_add_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ma) (le1 := le).
  - eapply exec_secp_read_field; [reflexivity|reflexivity|reflexivity|exact HA].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le).
    + eapply exec_secp_read_field; [reflexivity|reflexivity|reflexivity|exact HB].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * apply exec_secp_add_fields; exact HAdd.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
        -- eapply exec_secp_write_field; [reflexivity|reflexivity|exact HDst|exact HWrite].
        -- apply exec_Sreturn_some; constructor.
Qed.
Print Assumptions secp_fe_add_body.
Print Assumptions exec_secp_add_rest_calls.

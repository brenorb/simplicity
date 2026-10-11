(** Exact original three-local scalar-add statements and compositional calls. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_public_copy C.jet_secp_public_body.
Require Import C.jet_secp_scalar_public_entry C.jet_secp_scalar_public_calls C.jet_secp_scalar_normalize_rest.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_add_public_env bl ba bb : env :=
  PTree.set jets_secp._b (bb, (Tstruct __5826 noattr)) (scalar_public_env bl ba).
Definition scalar_add_read_stmt (id : ident) : statement :=
  Scall None
    (Evar jets_secp._read_scalar (Tfunction
      (Tcons (tptr (Tstruct __5826 noattr)) (Tcons (tptr secp_frame_type) Tnil)) tvoid cc_default))
    [Eaddrof (Evar id (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
     Eaddrof (Evar jets_secp._src secp_frame_type) (tptr secp_frame_type)].
Definition scalar_add_helper_stmt : statement :=
  Scall None
    (Evar jets_secp._secp256k1_scalar_add (Tfunction
      (Tcons (tptr (Tstruct __5826 noattr)) (Tcons (tptr (Tstruct __5826 noattr)) (Tcons (tptr (Tstruct __5826 noattr)) Tnil))) tint cc_default))
    [Eaddrof (Evar jets_secp._a (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
     Eaddrof (Evar jets_secp._a (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
     Eaddrof (Evar jets_secp._b (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition scalar_add_rest : statement :=
  Ssequence (scalar_add_read_stmt jets_secp._a)
    (Ssequence (scalar_add_read_stmt jets_secp._b)
      (Ssequence scalar_add_helper_stmt
        (Ssequence scalar_normalize_write_stmt
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))))).
Lemma scalar_add_body_eq :
  fn_body f_simplicity_scalar_add =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) scalar_add_rest.
Proof. reflexivity. Qed.
Lemma scalar_add_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._secp256k1_scalar_add =
    Some (secp_symbol_block jets_secp._secp256k1_scalar_add) /\
  Genv.find_funct secp_ge
    (Vptr (secp_symbol_block jets_secp._secp256k1_scalar_add) Ptrofs.zero) =
    Some (Internal f_secp256k1_scalar_add).
Proof. vm_compute; split; reflexivity. Qed.

Lemma exec_scalar_add_read e le m mf id ba bl :
  e!jets_secp._read_scalar = None ->
  e!id = Some (ba, (Tstruct __5826 noattr)) ->
  e!jets_secp._src = Some (bl, secp_frame_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (scalar_add_read_stmt id) E0 le mf Out_normal.
Proof.
  intros HGlobal HField HSource HCall.
  destruct scalar_public_read_symbols as [HRS HRF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._read_scalar) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero])
    (f := Internal f_read_scalar) (vres := Vundef).
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

Lemma exec_scalar_add_helper le m mf bl ba bb ret :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf (Vint ret) ->
  Clight2.exec_stmt secp_ge (scalar_add_public_env bl ba bb) le m
    scalar_add_helper_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct scalar_add_helper_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._secp256k1_scalar_add) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero])
    (f := Internal f_secp256k1_scalar_add) (vres := Vint ret).
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
      * eapply eval_Econs.
        -- apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
        -- reflexivity.
        -- apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_scalar_add_write e le m mf ba bd dbase :
  e!jets_secp._write_scalar = None -> e!jets_secp._a = Some (ba, (Tstruct __5826 noattr)) ->
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_scalar)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m scalar_normalize_write_stmt E0 le mf Out_normal.
Proof.
  intros HGlobal HField HDst HCall.
  destruct scalar_normalize_write_symbols as [HWS HWF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._write_scalar) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero])
    (f := Internal f_write_scalar) (vres := Vundef).
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

Lemma exec_scalar_add_rest_calls le m ma mb mn mf bl ba bb bd dbase ret :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef ->
  Clight2.eval_funcall secp_ge ma (Internal f_read_scalar)
    [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mb Vundef ->
  Clight2.eval_funcall secp_ge mb (Internal f_secp256k1_scalar_add)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mn (Vint ret) ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_scalar)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (scalar_add_public_env bl ba bb) le m scalar_add_rest E0 le mf
    (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HDst HA HB HAdd HWrite. unfold scalar_add_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ma) (le1 := le).
  - eapply exec_scalar_add_read; [reflexivity|reflexivity|reflexivity|exact HA].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le).
    + eapply exec_scalar_add_read; [reflexivity|reflexivity|reflexivity|exact HB].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * eapply exec_scalar_add_helper; exact HAdd.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
        -- eapply exec_scalar_add_write; [reflexivity|reflexivity|exact HDst|exact HWrite].
        -- apply exec_Sreturn_some; constructor.
Qed.
Print Assumptions scalar_add_body_eq.
Print Assumptions exec_scalar_add_rest_calls.


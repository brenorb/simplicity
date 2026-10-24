(** Exact original generate call spine and typed caller adapters. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
  C.jet_secp_scalar_add_body C.jet_secp_generate_entry C.jet_secp_generator_zero_global
  C.jet_clight_internal_frame C.jet_clight_internal_preserve
  C.jet_secp_field_io_preserve C.jet_secp_frame_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generate_helper := curve_call _secp256k1_ecmult f_secp256k1_ecmult None
  [Eaddrof (Evar _r (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
   Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
   Eaddrof (Evar _na (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
   Eaddrof (Evar _ng__2 (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition generate_write := curve_call _write_gej f_write_gej None
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));
   Eaddrof (Evar _r (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition generate_rest := Ssequence (scalar_add_read_stmt _ng__2)
  (Ssequence generate_helper (Ssequence generate_write (Sreturn (Some (Econst_int Int.one tint))))).
Lemma generate_body_source : fn_body f_simplicity_generate=Ssequence generate_copy generate_rest.
Proof. reflexivity. Qed.
Lemma generate_global_a : Genv.find_symbol secp_ge _a=Some (secp_symbol_block _a).
Proof. reflexivity. Qed.
Lemma generate_write_link : Genv.find_symbol secp_ge _write_gej=Some (secp_symbol_block _write_gej) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _write_gej) Ptrofs.zero)=Some (Internal f_write_gej).
Proof. split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_generate_helper le m mf bl bp bn :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult)
    [Vptr bp Ptrofs.zero;Vptr (secp_symbol_block _a) Ptrofs.zero;
     Vptr generator_zero_block Ptrofs.zero;Vptr bn Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (generate_public_env bl bp bn) le m generate_helper E0 le mf Out_normal.
Proof.
  intro Call;unfold generate_helper;eapply exec_curve_call with
    (vargs:=[Vptr bp Ptrofs.zero;Vptr (secp_symbol_block _a) Ptrofs.zero;
      Vptr generator_zero_block Ptrofs.zero;Vptr bn Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat first [left;reflexivity|right].
  - reflexivity.
  - eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);
      [apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
    eapply eval_Econs with (v1:=Vptr (secp_symbol_block _a) Ptrofs.zero).
    + apply eval_Eaddrof;apply eval_Evar_global;[reflexivity|exact generate_global_a].
    + reflexivity.
    + eapply eval_Econs with (v1:=Vptr generator_zero_block Ptrofs.zero);
        [apply eval_generator_zero_address;reflexivity|reflexivity|].
      eapply eval_Econs with (v1:=Vptr bn Ptrofs.zero);
        [apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_generate_write le m mf bl bp bn bd base :
  le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (generate_public_env bl bp bn) le m generate_write E0 le mf Out_normal.
Proof.
  intros Dst Call;unfold generate_write,curve_call.
  eapply exec_Scall with (vf:=Vptr (secp_symbol_block _write_gej) Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero]) (f:=Internal f_write_gej) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact (proj1 generate_write_link)]|
      apply deref_loc_reference;reflexivity].
  - eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
    eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
  - exact (proj2 generate_write_link).
  - reflexivity.
  - exact Call.
Qed.
Lemma exec_generate_rest le m mr mn mw bl bp bn bd base :
  le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
    [Vptr bn Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_ecmult)
    [Vptr bp Ptrofs.zero;Vptr (secp_symbol_block _a) Ptrofs.zero;
     Vptr generator_zero_block Ptrofs.zero;Vptr bn Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mw Vundef ->
  Clight2.exec_stmt secp_ge (generate_public_env bl bp bn) le m generate_rest E0 le mw
    (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros Dst Read Mult Write;unfold generate_rest.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mr).
  - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Read].
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mn);
      [eapply exec_generate_helper;exact Mult|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mw);
      [eapply exec_generate_write;[exact Dst|exact Write]|apply exec_Sreturn_some;constructor].
Qed.

Lemma generate_writer_closed : closed_stmtb field_io_helpers (fn_body f_write_gej)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma generate_writer_preserved m args trace mf result :
  Clight2.eval_funcall secp_ge m (Internal f_write_gej) args trace mf result -> readonly_preserved m mf.
Proof.
  apply function_preserved_from_body;[|reflexivity].
  intros e le mi t lef mo out Run Plain.
  exact (proj1 (internal_exec_preserved _ _ field_io_helpers_ok)
    e le mi _ t lef mo out Run Plain generate_writer_closed).
Qed.

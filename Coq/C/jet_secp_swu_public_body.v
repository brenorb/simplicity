(** Original public SWU statement tree and typed call adapters. The caller
    below must derive each call, not assume its output or execution. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_swu_public_boundary
  C.jet_secp_decompress_public_prepare C.jet_secp_rescale_public_body.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition swu_public_read := rescale_local_call _read_fe (Tstruct __5467 noattr)
  (Tstruct _frameItem noattr) _t _src.
Definition swu_public_map := rescale_local_call _shallue_van_de_woestijne
  (Tstruct __6121 noattr) (Tstruct __5467 noattr) _ge _t.
Definition swu_public_write := Scall None
  (Evar _write_ge (type_of_function f_write_ge))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));
   Eaddrof (Evar _ge (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Definition swu_public_rest := Ssequence swu_public_read
  (Ssequence swu_public_map (Ssequence swu_public_write (Sreturn (Some (Econst_int Int.one tint))))).
Lemma swu_public_source : fn_body f_simplicity_swu=Ssequence decompress_public_copy swu_public_rest.
Proof. reflexivity. Qed.
Lemma swu_public_symbols :
  (exists b,Genv.find_symbol secp_ge _read_fe=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_read_fe)) /\
  (exists b,Genv.find_symbol secp_ge _shallue_van_de_woestijne=Some b /\
    Genv.find_funct_ptr secp_ge b=Some (Internal f_shallue_van_de_woestijne)) /\
  (exists b,Genv.find_symbol secp_ge _write_ge=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_write_ge)).
Proof.
  split;[exists (secp_symbol_block _read_fe);split;reflexivity|].
  split;[exists (secp_symbol_block _shallue_van_de_woestijne);split;reflexivity|].
  exists (secp_symbol_block _write_ge);split;reflexivity.
Qed.
Local Opaque secp_ge.
Lemma exec_swu_public_write le m mf bl bt bp bd base : le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (swu_public_env bl bt bp) le m swu_public_write E0 le mf Out_normal.
Proof.
  intros Dst Call;destruct swu_public_symbols as (_ & _ & bf & Symbol & Fun).
  unfold swu_public_write;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero]) (f:=Internal f_write_ge) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
  - eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
    eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
  - exact Fun.
  - reflexivity.
  - exact Call.
Qed.
Lemma exec_swu_public_from_calls le m mr mn mf bl bt bp bd base :
  le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr bt Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_shallue_van_de_woestijne)
    [Vptr bp Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (swu_public_env bl bt bp) le m swu_public_rest E0 le mf
    (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros Dst Read Map Write;destruct swu_public_symbols as (RS & MS & WS);unfold swu_public_rest.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
  - unfold swu_public_read;eapply exec_rescale_local_call;
      [exact RS|reflexivity|reflexivity|reflexivity|reflexivity|exact Read].
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
    + unfold swu_public_map;eapply exec_rescale_local_call;
        [exact MS|reflexivity|reflexivity|reflexivity|reflexivity|exact Map].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
      * eapply exec_swu_public_write;[exact Dst|exact Write].
      * apply exec_Sreturn_some;constructor.
Qed.

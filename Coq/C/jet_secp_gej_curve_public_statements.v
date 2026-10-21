(** Actual public projective on-curve wrapper, including its bool temporary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_exec C.jet_readBit_layout C.jet_sx_exec C.jet_secp_linkage C.jets_secp
  C.jet_secp_gej_public_entry C.jet_secp_gej_predicate_body C.jet_secp_public_body C.jet_secp_odd_body.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition gej_curve_public_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_gej_is_on_curve)))).
Definition gej_curve_public_helper_stmt :=
  Scall (Some _t'1) (Evar _simplicity_gej_is_valid_var
    (Tfunction (Tcons (tptr (Tstruct __6123 noattr)) Tnil) tbool cc_default))
    [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition gej_curve_public_write_stmt := Scall None
  (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
    (Tcons tbool Tnil)) tbool cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));Etempvar _t'1 tbool].
Definition gej_curve_public_rest := Ssequence gej_predicate_read_stmt
  (Ssequence (Ssequence gej_curve_public_helper_stmt gej_curve_public_write_stmt)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma gej_curve_public_source : fn_body f_simplicity_gej_is_on_curve=
  Ssequence (Sassign (Evar _src (Tstruct _frameItem noattr))
    (Etempvar _src (Tstruct _frameItem noattr))) gej_curve_public_rest.
Proof. reflexivity. Qed.
Lemma gej_curve_public_ok : fn_okb f_simplicity_gej_is_on_curve=true.
Proof. reflexivity. Qed.
Lemma gej_curve_public_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,ba) ->
  function_entry2 secp_ge f_simplicity_gej_is_on_curve
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (gej_public_env bl ba) (gej_curve_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB;destruct (fn_okb_true _ gej_curve_public_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact HA|].
  eapply alloc_variables_cons with (m1:=mb) (b1:=ba);[exact HB|constructor].
Qed.
Lemma gej_curve_public_helper_symbol : exists b,
  Genv.find_symbol secp_ge _simplicity_gej_is_valid_var=Some b /\
  Genv.find_funct_ptr secp_ge b=Some (Internal f_simplicity_gej_is_valid_var).
Proof. exists (secp_symbol_block _simplicity_gej_is_valid_var);split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_gej_curve_public_helper le m mf bl ba bit :
  Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_curve_public_helper_stmt E0
    (PTree.set _t'1 (Vint (bit_int bit)) le) mf Out_normal.
Proof.
  intro HC;destruct gej_curve_public_helper_symbol as (b & HS & HF).
  unfold gej_curve_public_helper_stmt.
  eapply exec_Scall with (vf:=Vptr b Ptrofs.zero) (vargs:=[Vptr ba Ptrofs.zero])
    (f:=Internal f_simplicity_gej_is_valid_var) (vres:=Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[reflexivity|exact HS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_gej_curve_public_write e le m mf bd dbase bit :
  e!_writeBit=None -> le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'1=Some (Vint (bit_int bit)) ->
  Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge e le m gej_curve_public_write_stmt E0 le mf Out_normal.
Proof.
  intros HE HD HT HC;destruct secp_odd_helper_symbols as (HOS & HOF & HWS & HWF).
  unfold gej_curve_public_write_stmt.
  eapply exec_Scall with (vf:=Vptr (secp_symbol_block _writeBit) Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)])
    (f:=Internal C.jets.f_writeBit) (vres:=Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[exact HE|exact HWS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar;exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar;exact HT.
      * destruct bit;reflexivity.
      * apply eval_Enil.
  - exact HWF.
  - reflexivity.
  - exact HC.
Qed.

Theorem exec_gej_curve_public_rest_from_calls le m mr mn mf bl ba bd dbase bit :
  le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_gej)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_simplicity_gej_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mn (Vint (bit_int bit)) ->
  Clight2.eval_funcall secp_ge mn (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_curve_public_rest E0
    (PTree.set _t'1 (Vint (bit_int bit)) le) mf (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros HD HR HC HW;unfold gej_curve_public_rest.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
  - apply exec_gej_predicate_read;exact HR.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
      (le1:=PTree.set _t'1 (Vint (bit_int bit)) le).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn)
        (le1:=PTree.set _t'1 (Vint (bit_int bit)) le).
      * apply exec_gej_curve_public_helper;exact HC.
      * eapply exec_gej_curve_public_write.
        -- reflexivity.
        -- rewrite PTree.gso by discriminate;exact HD.
        -- apply PTree.gss.
        -- exact HW.
    + apply exec_Sreturn_some;constructor.
Qed.

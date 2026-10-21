(** Exact original public X-equivalence statements and both guard branches. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_exec C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_public_body C.jet_secp_public_copy C.jet_secp_curve_statements C.jet_secp_gej_predicate_body C.jet_secp_odd_body.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition x_equiv_public_env bl bq bp :=
  PTree.set _a (bp,Tstruct __6123 noattr) (PTree.set _x (bq,curve_fe_type)
    (PTree.set _src (bl,secp_frame_type) empty_env)).
Definition x_equiv_public_temps v_env bd dbase bs sbase :=
  PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_gej_x_equiv)))).
Definition x_equiv_public_point := Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr)).
Definition x_equiv_public_readq := curve_call _read_fe f_read_fe None
  [curve_local_address _x;Eaddrof (Evar _src secp_frame_type) (tptr secp_frame_type)].
Definition x_equiv_public_eq := curve_call _secp256k1_gej_eq_x_var f_secp256k1_gej_eq_x_var (Some _t'3)
  [curve_local_address _x;x_equiv_public_point].
Definition x_equiv_public_test := Ssequence gej_predicate_flag_stmt
  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
    (Ssequence x_equiv_public_eq (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
    (Sset _t'2 (Econst_int (Int.repr 0) tint))).
Definition x_equiv_public_write := Scall None
  (Evar _writeBit (Tfunction (Tcons (tptr secp_frame_type) (Tcons tbool Tnil)) tbool cc_default))
  [Etempvar _dst (tptr secp_frame_type);Etempvar _t'2 tint].
Definition x_equiv_public_rest := Ssequence x_equiv_public_readq
  (Ssequence gej_predicate_read_stmt (Ssequence
    (Ssequence x_equiv_public_test x_equiv_public_write)
    (Sreturn (Some (Econst_int (Int.repr 1) tint))))).
Definition x_equiv_branch_temps le (inf comp : bool) :=
  if inf then PTree.set _t'2 (Vint Int.zero) (PTree.set _t'1 (Vint Int.one) le)
  else PTree.set _t'2 (Vint (bit_int comp))
    (PTree.set _t'3 (Vint (bit_int comp)) (PTree.set _t'1 (Vint Int.zero) le)).

Lemma x_equiv_public_body_source : fn_body f_simplicity_gej_x_equiv =
  Ssequence (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) x_equiv_public_rest.
Proof. reflexivity. Qed.
Lemma x_equiv_public_ok : fn_okb f_simplicity_gej_x_equiv = true.
Proof. vm_compute;reflexivity. Qed.
Lemma x_equiv_public_entry v_env m ma mb mc bl bq bp bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,bq) -> Mem.alloc mb 0 128 = (mc,bp) ->
  function_entry2 secp_ge f_simplicity_gej_x_equiv
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (x_equiv_public_env bl bq bp) (x_equiv_public_temps v_env bd dbase bs sbase) mc.
Proof.
  intros HL HQ HP. destruct (fn_okb_true _ x_equiv_public_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact HL|].
  eapply alloc_variables_cons with (m1:=mb) (b1:=bq);[exact HQ|].
  eapply alloc_variables_cons with (m1:=mc) (b1:=bp);[exact HP|constructor].
Qed.

Local Ltac public_symbol :=
  unfold secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac public_args :=
  first [apply eval_Enil |
    eapply eval_Econs;
      [apply eval_Eaddrof;apply eval_Evar_local;reflexivity
      |reflexivity|public_args]].

Lemma exec_x_equiv_public_readq le m mf bl bq bp :
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr bq Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m x_equiv_public_readq E0 le mf Out_normal.
Proof.
  intro HC. unfold x_equiv_public_readq,curve_call.
  destruct secp_public_helper_symbols as (HS & HF & HWS & HWF).
  eapply exec_Scall with (vf:=Vptr (secp_symbol_block _read_fe) Ptrofs.zero)
    (vargs:=[Vptr bq Ptrofs.zero;Vptr bl Ptrofs.zero]) (f:=Internal f_read_fe) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[reflexivity|exact HS].
    + apply deref_loc_reference;reflexivity.
  - public_args.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.
Lemma exec_x_equiv_public_readpoint le m mf bl bq bp :
  Clight2.eval_funcall secp_ge m (Internal f_read_gej)
    [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m gej_predicate_read_stmt E0 le mf Out_normal.
Proof.
  intro HC. change (Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m
    (curve_call _read_gej f_read_gej None
      [x_equiv_public_point;Eaddrof (Evar _src secp_frame_type) (tptr secp_frame_type)]) E0 le mf Out_normal).
  destruct gej_predicate_reader_symbol as (b & HS & HF).
  eapply exec_Scall with (vf:=Vptr b Ptrofs.zero)
    (vargs:=[Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero]) (f:=Internal f_read_gej) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[reflexivity|exact HS].
    + apply deref_loc_reference;reflexivity.
  - public_args.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.
Lemma exec_x_equiv_public_flag le m bl bq bp flag :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_is_infinity)
    [Vptr bp Ptrofs.zero] E0 m (Vint flag) ->
  Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m gej_predicate_flag_stmt E0
    (PTree.set _t'1 (Vint flag) le) m Out_normal.
Proof.
  intro HC. change (Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m
    (curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity (Some _t'1)
      [x_equiv_public_point]) E0 (PTree.set _t'1 (Vint flag) le) m Out_normal).
  eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vint flag).
  - public_symbol.
  - reflexivity.
  - public_args.
  - exact HC.
Qed.

Theorem exec_x_equiv_public_test le m mf bl bq bp (inf comp : bool) :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_is_infinity)
    [Vptr bp Ptrofs.zero] E0 m (Vint (bit_int inf)) ->
  (if inf then mf=m else Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_x_var)
    [Vptr bq Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf (Vint (bit_int comp))) ->
  Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m x_equiv_public_test E0
    (x_equiv_branch_temps le inf comp) mf Out_normal.
Proof.
  intros CF CE. unfold x_equiv_public_test,x_equiv_branch_temps.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'1 (Vint (bit_int inf)) le).
  - apply exec_x_equiv_public_flag;exact CF.
  - destruct inf;cbn [bit_int] in *.
    + subst mf. eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
      * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
      * reflexivity.
      * apply exec_Sset;constructor.
    + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
      * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
      * reflexivity.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
          (le1:=PTree.set _t'3 (Vint (bit_int comp)) (PTree.set _t'1 (Vint Int.zero) le)).
        -- unfold x_equiv_public_eq. eapply exec_curve_call with
             (vargs:=[Vptr bq Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vint (bit_int comp)).
           ++ public_symbol.
           ++ reflexivity.
           ++ public_args.
           ++ exact CE.
        -- apply exec_Sset. eapply eval_Ecast.
           ++ apply eval_Etempvar;apply PTree.gss.
           ++ destruct comp;reflexivity.
Qed.

Lemma x_equiv_branch_dst le inf comp v : le!_dst=Some v ->
  (x_equiv_branch_temps le inf comp)!_dst=Some v.
Proof.
  intro HD;unfold x_equiv_branch_temps;destruct inf;
    rewrite !PTree.gso by discriminate;exact HD.
Qed.
Lemma x_equiv_branch_bit le inf comp :
  (x_equiv_branch_temps le inf comp)!_t'2 = Some (Vint (bit_int (andb (negb inf) comp))).
Proof. unfold x_equiv_branch_temps;destruct inf;apply PTree.gss. Qed.

Lemma exec_x_equiv_public_write e le m mf bd dbase bit :
  e!_writeBit=None -> le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'2=Some (Vint (bit_int bit)) ->
  Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge e le m x_equiv_public_write E0 le mf Out_normal.
Proof.
  intros HE HD HT HC. destruct secp_odd_helper_symbols as (HOS & HOF & HS & HF).
  eapply exec_Scall with (vf:=Vptr (secp_symbol_block _writeBit) Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)])
    (f:=Internal C.jets.f_writeBit) (vres:=Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[exact HE|exact HS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar;exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar;exact HT.
      * destruct bit;reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.

Theorem exec_x_equiv_public_rest_from_calls le m mq mr mn mf bl bq bp bd dbase inf comp :
  le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr bq Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mq Vundef ->
  Clight2.eval_funcall secp_ge mq (Internal f_read_gej)
    [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_gej_is_infinity)
    [Vptr bp Ptrofs.zero] E0 mr (Vint (bit_int inf)) ->
  (if inf then mn=mr else Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_gej_eq_x_var)
    [Vptr bq Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mn (Vint (bit_int comp))) ->
  Clight2.eval_funcall secp_ge mn (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase);Vint (bit_int (andb (negb inf) comp))] E0 mf
    (Vint (bit_int (andb (negb inf) comp))) ->
  Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m x_equiv_public_rest E0
    (x_equiv_branch_temps le inf comp) mf (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros HD CQ CP CF CE CW. unfold x_equiv_public_rest.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mq) (le1:=le).
  - apply exec_x_equiv_public_readq;exact CQ.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
    + apply exec_x_equiv_public_readpoint;exact CP.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
        (le1:=x_equiv_branch_temps le inf comp).
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn)
          (le1:=x_equiv_branch_temps le inf comp).
        -- apply exec_x_equiv_public_test;assumption.
        -- eapply exec_x_equiv_public_write.
           ++ reflexivity.
           ++ apply x_equiv_branch_dst;exact HD.
           ++ apply x_equiv_branch_bit.
           ++ exact CW.
      * apply exec_Sreturn_some;constructor.
Qed.

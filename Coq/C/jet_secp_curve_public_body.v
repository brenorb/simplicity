(** Exact public affine curve-check statements and entry. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_readBit_layout C.jet_sx_exec C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_owned_public_lifecycle.
Require Import C.jet_secp_ge_negate_boundary C.jet_secp_odd_body C.jet_secp_gej_predicate_body.
Import ListNotations Clightdefs Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition curve_public_temps v_env bd dbase bs sbase :=
  PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_ge_is_on_curve)))).
Lemma curve_public_ok : fn_okb f_simplicity_ge_is_on_curve = true.
Proof. vm_compute; reflexivity. Qed.
Lemma curve_public_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 88 = (mb,ba) ->
  function_entry2 secp_ge f_simplicity_ge_is_on_curve
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (ge_public_env bl ba) (curve_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB. destruct (fn_okb_true _ curve_public_ok) as (HN1 & HN2 & HD).
  constructor; [exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl).
  - exact HA.
  - eapply alloc_variables_cons with (m1:=mb) (b1:=ba); [exact HB|constructor].
Qed.
Definition curve_public_check_stmt :=
  Scall (Some _t'1) (Evar _secp256k1_ge_is_valid_var
    (Tfunction (Tcons (tptr (Tstruct __6121 noattr)) Tnil) tint cc_default))
    [Eaddrof (Evar _a (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Definition curve_public_rest :=
  Ssequence ge_public_read_stmt
    (Ssequence (Ssequence curve_public_check_stmt secp_public_bit_write_stmt)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).
Lemma curve_public_body_source : fn_body f_simplicity_ge_is_on_curve =
  Ssequence (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) curve_public_rest.
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Lemma exec_curve_public_check le m mf bl ba flag :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf (Vint flag) ->
  Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m curve_public_check_stmt E0
    (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
  intro HC.
  destruct (secp_pure_ok _secp256k1_ge_is_valid_var f_secp256k1_ge_is_valid_var
    ltac:(unfold secp_pure; repeat (first [left;reflexivity|right]))) as (b & HS & HF).
  unfold curve_public_check_stmt.
  eapply exec_Scall with (vf:=Vptr b Ptrofs.zero) (vargs:=[Vptr ba Ptrofs.zero])
    (f:=Internal f_secp256k1_ge_is_valid_var) (vres:=Vint flag).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_ge_is_valid_var)); exact HF.
  - reflexivity.
  - exact HC.
Qed.
Lemma exec_curve_public_rest_from_calls le m mr mn mf bl ba bd dbase bit :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_ge)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_ge_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mn (Vint (bit_int bit)) ->
  Clight2.eval_funcall secp_ge mn (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m curve_public_rest E0
    (PTree.set _t'1 (Vint (bit_int bit)) le) mf (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros HD HR HC HW; unfold curve_public_rest.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
  - apply exec_ge_public_read; exact HR.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
      (le1:=PTree.set _t'1 (Vint (bit_int bit)) le).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn)
        (le1:=PTree.set _t'1 (Vint (bit_int bit)) le).
      * apply exec_curve_public_check; exact HC.
      * eapply exec_secp_bit_write_in_env.
        -- reflexivity.
        -- rewrite PTree.gso by discriminate; exact HD.
        -- apply PTree.gss.
        -- exact HW.
    + apply exec_Sreturn_some; constructor.
Qed.

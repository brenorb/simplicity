(** Actual public affine entry and generated call tree; final proof derives calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy C.jet_secp_public_body.
Require Import C.jet_secp_owned_public_lifecycle.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ge_public_env bl ba := owned_public_env (Tstruct __6121 noattr) bl ba.
Lemma ge_negate_public_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 88 = (mb,ba) ->
  function_entry2 secp_ge f_simplicity_ge_negate
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (ge_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros x y HX HY Hxy;cbn in HX,HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;subst;
      first [contradiction|vm_compute in Hxy;discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma,bl));exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 88 = (mb,ba));exact HB.
      * constructor.
  - reflexivity.
Qed.

Definition ge_public_read_stmt :=
  Scall None (Evar _read_ge (Tfunction
    (Tcons (tptr (Tstruct __6121 noattr)) (Tcons (tptr secp_frame_type) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _a (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
     Eaddrof (Evar _src secp_frame_type) (tptr secp_frame_type)].
Definition ge_negate_call_stmt :=
  Scall None (Evar _secp256k1_ge_neg (Tfunction
    (Tcons (tptr (Tstruct __6121 noattr))
      (Tcons (tptr (Tstruct __6121 noattr)) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _a (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
     Eaddrof (Evar _a (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Definition ge_public_write_stmt :=
  Scall None (Evar _write_ge (Tfunction
    (Tcons (tptr secp_frame_type) (Tcons (tptr (Tstruct __6121 noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr secp_frame_type);
     Eaddrof (Evar _a (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Definition ge_negate_public_rest :=
  Ssequence ge_public_read_stmt (Ssequence ge_negate_call_stmt
    (Ssequence ge_public_write_stmt (Sreturn (Some (Econst_int (Int.repr 1) tint))))).
Lemma ge_negate_public_body : fn_body f_simplicity_ge_negate =
  Ssequence (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) ge_negate_public_rest.
Proof. reflexivity. Qed.

Lemma ge_negate_public_symbol id f :
  In (id,f) [(_read_ge,f_read_ge);(_secp256k1_ge_neg,f_secp256k1_ge_neg);(_write_ge,f_write_ge)] ->
  exists b, Genv.find_symbol secp_ge id = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f).
Proof.
  intro HIn;exists (secp_symbol_block id).
  destruct HIn as [H|[H|[H|H]]];[| | |contradiction];
    pose proof (f_equal (@fst ident function) H) as Hid;
    pose proof (f_equal (@snd ident function) H) as Hf;
    cbn [fst snd] in Hid,Hf;subst id f;split;reflexivity.
Qed.
Local Opaque secp_ge.

Lemma exec_ge_public_read le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_read_ge)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m ge_public_read_stmt E0 le mf Out_normal.
Proof.
  intro HC;destruct (ge_negate_public_symbol _read_ge f_read_ge ltac:(left;reflexivity)) as (b&HS&HF).
  unfold ge_public_read_stmt.
  eapply exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero]) (f := Internal f_read_ge) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[reflexivity|exact HS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_read_ge));exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_ge_negate_call le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_neg)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m ge_negate_call_stmt E0 le mf Out_normal.
Proof.
  intro HC;destruct (ge_negate_public_symbol _secp256k1_ge_neg f_secp256k1_ge_neg
    ltac:(right;left;reflexivity)) as (b&HS&HF).
  unfold ge_negate_call_stmt.
  eapply exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero]) (f := Internal f_secp256k1_ge_neg) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[reflexivity|exact HS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_ge_neg));exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_ge_public_writer le m mf bl ba bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m ge_public_write_stmt E0 le mf Out_normal.
Proof.
  intros HD HC;destruct (ge_negate_public_symbol _write_ge f_write_ge
    ltac:(right;right;left;reflexivity)) as (b&HS&HF).
  unfold ge_public_write_stmt.
  eapply exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero]) (f := Internal f_write_ge) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global;[reflexivity|exact HS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar;exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_write_ge));exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_ge_negate_rest_from_calls le m mr mn mf bl ba bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_ge)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_ge_neg)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m ge_negate_public_rest E0 le mf
    (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros HD HR HN HW;unfold ge_negate_public_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
  - apply exec_ge_public_read;exact HR.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
    + apply exec_ge_negate_call;exact HN.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
      * eapply exec_ge_public_writer;eassumption.
      * apply exec_Sreturn_some;constructor.
Qed.
Print Assumptions ge_negate_public_entry.
Timeout 60 Print Assumptions exec_ge_negate_rest_from_calls.

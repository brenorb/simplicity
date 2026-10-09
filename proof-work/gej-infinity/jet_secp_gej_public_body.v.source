(** Exact public point-infinity body and compositional call adapters. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_gej_public_entry C.jet_secp_public_copy.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition gej_public_init_stmt :=
  Scall None (Evar _secp256k1_gej_set_infinity
    (Tfunction (Tcons (tptr (Tstruct __6123 noattr)) Tnil) tvoid cc_default))
    [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition gej_public_write_stmt :=
  Scall None (Evar _write_gej (Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct __6123 noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition gej_public_rest := Ssequence gej_public_init_stmt
  (Ssequence gej_public_write_stmt (Sreturn (Some (Econst_int (Int.repr 1) tint)))).
Lemma gej_public_body : fn_body f_simplicity_gej_infinity =
  Ssequence (Sassign (Evar _src (Tstruct _frameItem noattr))
    (Etempvar _src (Tstruct _frameItem noattr))) gej_public_rest.
Proof. reflexivity. Qed.

Lemma gej_public_writer_symbol :
  exists b, Genv.find_symbol secp_ge _write_gej = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_write_gej).
Proof. exists (secp_symbol_block _write_gej); split; reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_gej_public_initializer le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_infinity)
    [Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m
    gej_public_init_stmt E0 le mf Out_normal.
Proof.
  intro HC.
  destruct (secp_pure_ok _secp256k1_gej_set_infinity f_secp256k1_gej_set_infinity
    ltac:(unfold secp_pure; repeat (first [left; reflexivity|right]))) as (b & HS & HF).
  unfold gej_public_init_stmt.
  eapply ClightBigstep.exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero]) (f := Internal f_secp256k1_gej_set_infinity)
    (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_gej_set_infinity)); exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_gej_public_writer le m mf bl ba bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m
    gej_public_write_stmt E0 le mf Out_normal.
Proof.
  intros HD HC; destruct gej_public_writer_symbol as (b & HS & HF).
  unfold gej_public_write_stmt.
  eapply ClightBigstep.exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero])
    (f := Internal f_write_gej) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_write_gej)); exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_gej_public_rest_from_calls le m mi mf bl ba bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_infinity)
    [Vptr ba Ptrofs.zero] E0 mi Vundef ->
  Clight2.eval_funcall secp_ge mi (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_public_rest E0 le mf
    (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HD HI HW; unfold gej_public_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := le).
  - apply exec_gej_public_initializer; exact HI.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
    + eapply exec_gej_public_writer; eassumption.
    + apply exec_Sreturn_some; constructor.
Qed.
Print Assumptions exec_gej_public_rest_from_calls.

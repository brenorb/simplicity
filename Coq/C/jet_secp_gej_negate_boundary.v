(** Original point-negation boundary. Internal adapters retain explicit call
    premises; these are NOT a public implementation-to-specification theorem. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp C.jet_secp_zero_entry.
Require Import C.jet_secp_public_copy C.jet_secp_gej_public_entry C.jet_secp_gej_public_body.
Require Import C.jet_secp_gej_predicate_body.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma gej_negate_public_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 128 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_gej_negate
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (gej_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB.
  eapply function_entry2_same_declarations with (f := f_simplicity_gej_infinity).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply gej_infinity_public_entry; eassumption.
Qed.

Definition gej_negate_call_stmt : statement :=
  Scall None (Evar _secp256k1_gej_neg (Tfunction
    (Tcons (tptr (Tstruct __6123 noattr))
      (Tcons (tptr (Tstruct __6123 noattr)) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
     Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition gej_negate_public_rest : statement :=
  Ssequence gej_predicate_read_stmt
    (Ssequence gej_negate_call_stmt
      (Ssequence gej_public_write_stmt (Sreturn (Some (Econst_int (Int.repr 1) tint))))).
Lemma gej_negate_public_body : fn_body f_simplicity_gej_negate =
  Ssequence (Sassign (Evar _src (Tstruct _frameItem noattr))
    (Etempvar _src (Tstruct _frameItem noattr))) gej_negate_public_rest.
Proof. reflexivity. Qed.
Lemma gej_negate_helper_symbol :
  exists b, Genv.find_symbol secp_ge _secp256k1_gej_neg = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_gej_neg).
Proof. exists (secp_symbol_block _secp256k1_gej_neg); split; reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_gej_negate_call le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_neg)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m
    gej_negate_call_stmt E0 le mf Out_normal.
Proof.
  intro HC; destruct gej_negate_helper_symbol as (b & HS & HF).
  unfold gej_negate_call_stmt.
  eapply ClightBigstep.exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero])
    (f := Internal f_secp256k1_gej_neg) (vres := Vundef).
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
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_gej_neg)); exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_gej_negate_rest_from_calls le m mr mn mf bl ba bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_gej)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_gej_neg)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m
    gej_negate_public_rest E0 le mf (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HD HR HN HW; unfold gej_negate_public_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
  - apply exec_gej_predicate_read; exact HR.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
    + apply exec_gej_negate_call; exact HN.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
      * eapply exec_gej_public_writer; eassumption.
      * apply exec_Sreturn_some; constructor.
Qed.
Print Assumptions gej_negate_public_entry.
Timeout 60 Print Assumptions exec_gej_negate_rest_from_calls.

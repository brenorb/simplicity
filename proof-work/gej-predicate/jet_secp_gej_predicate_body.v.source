(** Exact public point-predicate statements and reusable bit-write adapter. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps Globalenvs.
Require Import C.jet_exec C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_gej_public_entry C.jet_secp_public_body C.jet_secp_odd_body.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition gej_predicate_read_stmt : statement :=
  Scall None (Evar _read_gej (Tfunction
    (Tcons (tptr (Tstruct __6123 noattr))
      (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
     Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition gej_predicate_flag_stmt : statement :=
  Scall (Some _t'1) (Evar _secp256k1_gej_is_infinity (Tfunction
    (Tcons (tptr (Tstruct __6123 noattr)) Tnil) tint cc_default))
    [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition gej_predicate_rest : statement :=
  Ssequence gej_predicate_read_stmt
    (Ssequence (Ssequence gej_predicate_flag_stmt secp_public_bit_write_stmt)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).
Lemma gej_predicate_body : fn_body f_simplicity_gej_is_infinity =
  Ssequence (Sassign (Evar _src (Tstruct _frameItem noattr))
    (Etempvar _src (Tstruct _frameItem noattr))) gej_predicate_rest.
Proof. reflexivity. Qed.
Lemma gej_predicate_reader_symbol :
  exists b, Genv.find_symbol secp_ge _read_gej = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_read_gej).
Proof. exists (secp_symbol_block _read_gej); split; reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_gej_predicate_read le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_read_gej)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m
    gej_predicate_read_stmt E0 le mf Out_normal.
Proof.
  intro HC; destruct gej_predicate_reader_symbol as (b & HS & HF).
  unfold gej_predicate_read_stmt.
  eapply ClightBigstep.exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero])
    (f := Internal f_read_gej) (vres := Vundef).
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
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_read_gej)); exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_gej_predicate_flag le m mf bl ba flag :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_is_infinity)
    [Vptr ba Ptrofs.zero] E0 mf (Vint flag) ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_predicate_flag_stmt E0
    (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
  intro HC.
  destruct (secp_pure_ok _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity
    ltac:(unfold secp_pure; repeat (first [left;reflexivity|right]))) as (b & HS & HF).
  unfold gej_predicate_flag_stmt.
  eapply ClightBigstep.exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero])
    (f := Internal f_secp256k1_gej_is_infinity) (vres := Vint flag).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_gej_is_infinity)); exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_secp_bit_write_in_env e le m mf bd dbase (bit : bool) :
  e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'1 = Some (Vint (bit_int bit)) ->
  Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge e le m secp_public_bit_write_stmt E0 le mf Out_normal.
Proof.
  intros HE HD HT HC; destruct secp_odd_helper_symbols as (HOS & HOF & HWS & HWF).
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _writeBit) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase);Vint (bit_int bit)])
    (f := Internal C.jets.f_writeBit) (vres := Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * exact HE.
      * exact HWS.
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar; exact HT.
      * destruct bit; reflexivity.
      * apply eval_Enil.
  - exact HWF.
  - reflexivity.
  - exact HC.
Qed.

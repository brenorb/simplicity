From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Require Import C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_readBit_layout
 C.jet_secp_rescale_public_reads C.jet_secp_gej_curve_prefix C.jet_secp_gej_curve_function
 C.jet_secp_gej_curve_literal_bridge C.jet_secp_scale_public_support C.jet_secp_curve_literal
 C.jet_secp_fe_nv C.jet_secp_multiply_finish_product C.jet_secp_square_spec_bridge.
Require Import C.jet_secp_multiply_normalize_bridge.
Lemma checked_curve_helper_closed : closed_stmtb secp_closed_helpers (fn_body f_simplicity_gej_is_valid_var)=true.

Proof. vm_compute;reflexivity. Qed.

Lemma checked_curve_helper_preserved m args t mf result : Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var) args t mf result -> readonly_preserved m mf.

Proof. apply secp_closed_function_preserved;[exact checked_curve_helper_closed|reflexivity]. Qed.

Theorem eval_checked_validity_literal x y z m ba :
 fe_at m ba 0 (words5 (square_reader_rho x)) ->
 fe_at m ba 40 (words5 (square_reader_rho y)) ->
 fe_at m ba 80 (words5 (square_reader_rho z)) ->
 Mem.range_perm m ba 0 128 Cur Freeable ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var) [Vptr ba Ptrofs.zero] E0 mf
  (Vint (bit_int (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))))) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\
 lframe (fun b _=>b<>ba) m mf /\
 gej_curve_input_readback m mf ba (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) /\
 readonly_preserved m mf.
Proof.
 intros X Y Z Owned.
 destruct (eval_gej_curve_function_readback (square_reader_rho x) (square_reader_rho y) (square_reader_rho z)
  m ba (square_reader_bounds x) (square_reader_bounds y) (square_reader_bounds z) X Y Z Owned)
 as (mf & Call & Free & Frame & Readback).
 exists mf;split;[rewrite gej_curve_result_matches_literal in Call;exact Call|].
 split;[exact Free|];split;[exact Frame|];split;[exact Readback|].
 eapply checked_curve_helper_preserved;exact Call.
Qed.

Definition checked_curve_stmt := Scall (Some _t'1)
 (Evar _simplicity_gej_is_valid_var (Tfunction (Tcons (tptr (Tstruct __6123 noattr)) Tnil) tbool cc_default))
 [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Lemma checked_curve_symbol : exists b,
 Genv.find_symbol secp_ge _simplicity_gej_is_valid_var=Some b /\
 Genv.find_funct_ptr secp_ge b=Some (Internal f_simplicity_gej_is_valid_var).
Proof. exists (secp_symbol_block _simplicity_gej_is_valid_var);split;reflexivity. Qed.
Lemma exec_checked_curve le m mf bl br ba bk bit :
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var) [Vptr ba Ptrofs.zero]
 E0 mf (Vint (bit_int bit)) ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le m checked_curve_stmt E0
 (PTree.set _t'1 (Vint (bit_int bit)) le) mf Out_normal.
Proof.
 intro Call;destruct checked_curve_symbol as (b & Symbol & Function).
 unfold checked_curve_stmt.
 eapply exec_Scall with (vf:=Vptr b Ptrofs.zero) (vargs:=[Vptr ba Ptrofs.zero])
  (f:=Internal f_simplicity_gej_is_valid_var) (vres:=Vint (bit_int bit)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.

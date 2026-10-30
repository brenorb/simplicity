(** Actual named-call boundary for the linked wNAF implementation. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_parse_start.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_wnaf_lookup:
 secp_helper_lookup elements_taptweak_ge(_secp256k1_ecmult_wnaf,f_secp256k1_ecmult_wnaf)=
 Some(Internal f_secp256k1_ecmult_wnaf).
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.
Lemma exec_elements_taptweak_wnaf_call result args vargs v e le m mf:
 e!_secp256k1_ecmult_wnaf=None ->
 eval_exprlist elements_taptweak_ge e le m args(type_of_params(fn_params f_secp256k1_ecmult_wnaf))vargs ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal f_secp256k1_ecmult_wnaf)vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m
 (curve_call _secp256k1_ecmult_wnaf f_secp256k1_ecmult_wnaf result args)E0(set_opttemp result v le)mf Out_normal.
Proof.
 intros Global Args Call.
 destruct(secp_helper_lookup_exists elements_taptweak_ge _ _ elements_taptweak_wnaf_lookup)as(bf & Symbol & Funct).
 eapply exec_elements_taptweak_curve_call with(bf:=bf);[exact Symbol| |exact Global|exact Args|exact Call].
 unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
Qed.

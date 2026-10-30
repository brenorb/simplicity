(** Discharge every context-transport interface fact for the concrete linked
    program; no layout or symbol premise escapes these specialized helpers. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight Globalenvs.
Require Import C.jet_transport C.jet_sha_linkage C.jet_sha_uchars_prep
 C.jet_elements_taptweak_pure.
Require Import C.jet_sha_context_transport C.jet_elements_taptweak_globals.
Require C.jets_sha.
Set Default Timeout 10.
Lemma elements_taptweak_sha_context_checked k id:
 expr_okb sha_ge elements_taptweak_ge (ctx_field_expr k id)=true.
Proof. destruct k;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_counter_symbol:
 Genv.find_symbol elements_taptweak_ge jets_sha._sha256_max_counter=
 Some elements_taptweak_sha_counter_block.
Proof. vm_compute;reflexivity. Qed.
Definition eval_elements_taptweak_ctx_field_lvalue:=
 @eval_sha_context_field_lvalue_at elements_taptweak_ge elements_taptweak_sha_context_checked.
Definition eval_elements_taptweak_ctx_field:=
 @eval_sha_context_field_at elements_taptweak_ge elements_taptweak_sha_context_checked.
Definition eval_elements_taptweak_ctx_block:=
 @eval_sha_context_block_at elements_taptweak_ge elements_taptweak_sha_context_checked.
Definition exec_elements_taptweak_ctx_assign:=
 @exec_sha_context_assign_at elements_taptweak_ge elements_taptweak_sha_context_checked.
Definition exec_elements_taptweak_sha_available_overflow:=
 @exec_sha_available_overflow_at elements_taptweak_ge elements_taptweak_sha_counter_block
 elements_taptweak_sha_context_checked elements_taptweak_sha_counter_symbol.

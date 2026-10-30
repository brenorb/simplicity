(** Bind the original x-only pointer checks, clear and call rules to the
    actual linked program. Layout and helper lookup are discharged here. *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Globalenvs Memory Values Events.
Require Import C.jets_secp C.jet_secp_wnaf_memset C.jet_memset_model
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals
 C.jet_xonly_parse_control_at C.jet_xonly_parse_clear_at.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_xonly_key_size:
 sizeof (genv_cenv elements_taptweak_ge) (Tstruct __6478 noattr)=64.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_memset_linked:
 exists bf,Genv.find_symbol elements_taptweak_ge _memset=Some bf /\
 Genv.find_funct elements_taptweak_ge (Vptr bf Ptrofs.zero)=
 Some (External (EF_external "memset" memset_sig)
 (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof.
 exists (elements_taptweak_symbol_block _memset);vm_compute;split;reflexivity.
Qed.
Definition exec_elements_taptweak_xonly_parse_clear:=exec_xonly_parse_clear_at
 elements_taptweak_ge elements_taptweak_xonly_key_size elements_taptweak_memset_linked.
Definition exec_elements_taptweak_xonly_parse_start:=exec_xonly_parse_start_at
 elements_taptweak_ge elements_taptweak_xonly_key_size elements_taptweak_memset_linked.
Definition exec_elements_taptweak_curve_call:=exec_curve_call_at elements_taptweak_ge.
Definition exec_elements_taptweak_xonly_guard_one:=exec_xonly_guard_one_at elements_taptweak_ge.
Definition exec_elements_taptweak_xonly_guard_zero:=exec_xonly_guard_zero_at elements_taptweak_ge.
Definition eval_elements_taptweak_xonly_correct_subgroup:=eval_xonly_correct_subgroup_at elements_taptweak_ge.

(** Actual linked x-only tweak entry. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jets_secp C.jet_secp_linkage C.jet_secp_xonly_tweak_entry
 C.jet_elements_taptweak_pure C.jet_transport C.jet_transport_entry
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations.
Set Default Timeout 10.
Local Open Scope Z_scope.
Lemma elements_taptweak_xonly_tweak_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_xonly_pubkey_tweak_add)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Theorem elements_taptweak_xonly_tweak_entry m output input bytes:exists mi bk,
 function_entry2 elements_taptweak_ge f_secp256k1_xonly_pubkey_tweak_add[output;input;bytes]m
 (xonly_tweak_env bk)(xonly_tweak_temps output input bytes)mi /\
 (forall b,Mem.valid_block m b ->b<>bk) /\Mem.range_perm mi bk 0 88 Cur Freeable /\
 lframe(fun _ _=>True)m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct(xonly_tweak_entry m output input bytes)as(mi & bk & Entry & Rest).
 exists mi,bk;split;[eapply function_entry2_transport;[exact elements_taptweak_xonly_tweak_vars_checked|exact Entry]|exact Rest].
Qed.

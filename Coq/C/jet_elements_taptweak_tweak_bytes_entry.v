(** Actual linked byte-scalar tweak entry and two local frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_sx_exec C.jet_sx_mem C.jet_secp_local_regions C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_tweak_bytes_entry C.jet_elements_taptweak_pure C.jet_transport C.jet_transport_entry.
Lemma elements_taptweak_tweak_bytes_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_ec_pubkey_tweak_add_helper)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_tweak_bytes_blocks bt bf:
 blocks_of_env elements_taptweak_ge(tweak_bytes_env bt bf)=[(bf,0,4);(bt,0,32)].
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Theorem elements_taptweak_tweak_bytes_entry m bk bb:exists mi bt bf,
 function_entry2 elements_taptweak_ge f_secp256k1_ec_pubkey_tweak_add_helper[Vptr bk Ptrofs.zero;Vptr bb Ptrofs.zero]
 m(tweak_bytes_env bt bf)(tweak_bytes_temps bk bb)mi /\bt<>bf /\
 (forall b,Mem.valid_block m b ->b<>bt /\b<>bf) /\
 Mem.range_perm mi bt 0 32 Cur Freeable /\Mem.range_perm mi bf 0 4 Cur Freeable /\
 lframe(fun _ _=>True)m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct(tweak_bytes_entry m bk bb)as(mi & bt & bf & Entry & Rest).
 exists mi,bt,bf;split;[eapply function_entry2_transport;[exact elements_taptweak_tweak_bytes_vars_checked|exact Entry]|exact Rest].
Qed.
Theorem elements_taptweak_tweak_bytes_free m bt bf:bt<>bf ->Mem.range_perm m bt 0 32 Cur Freeable ->
 Mem.range_perm m bf 0 4 Cur Freeable ->exists mf,
 Mem.free_list m(blocks_of_env elements_taptweak_ge(tweak_bytes_env bt bf))=Some mf /\
 lframe(fun b _=>b<>bt /\b<>bf)m mf /\readonly_preserved m mf.
Proof.
 intros Sep FP FO;destruct(tweak_bytes_free m bt bf Sep FP FO)as(mf & Free & Rest).
 exists mf;split;[rewrite elements_taptweak_tweak_bytes_blocks;rewrite tweak_bytes_blocks in Free;exact Free|exact Rest].
Qed.

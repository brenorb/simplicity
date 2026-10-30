(** Actual linked native tweak entry and two local frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_sx_exec C.jet_sx_mem C.jet_secp_local_regions C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_eckey_tweak_entry C.jet_elements_taptweak_pure C.jet_transport C.jet_transport_entry.
Lemma elements_taptweak_eckey_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_eckey_pubkey_tweak_add)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_eckey_blocks bp bo:
 blocks_of_env elements_taptweak_ge(eckey_tweak_env bp bo)=[(bo,0,32);(bp,0,128)].
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Theorem elements_taptweak_eckey_entry m bk bt:exists mi bp bo,
 function_entry2 elements_taptweak_ge f_secp256k1_eckey_pubkey_tweak_add[Vptr bk Ptrofs.zero;Vptr bt Ptrofs.zero]
 m(eckey_tweak_env bp bo)(eckey_tweak_temps bk bt)mi /\bp<>bo /\
 (forall b,Mem.valid_block m b ->b<>bp /\b<>bo) /\
 Mem.range_perm mi bp 0 128 Cur Freeable /\Mem.range_perm mi bo 0 32 Cur Freeable /\
 lframe(fun _ _=>True)m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct(eckey_tweak_entry m bk bt)as(mi & bp & bo & Entry & Rest).
 exists mi,bp,bo;split;[eapply function_entry2_transport;[exact elements_taptweak_eckey_vars_checked|exact Entry]|exact Rest].
Qed.
Theorem elements_taptweak_eckey_free m bp bo:bp<>bo ->Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bo 0 32 Cur Freeable ->exists mf,
 Mem.free_list m(blocks_of_env elements_taptweak_ge(eckey_tweak_env bp bo))=Some mf /\
 lframe(fun b _=>b<>bp /\b<>bo)m mf /\readonly_preserved m mf.
Proof.
 intros Sep FP FO;destruct(eckey_tweak_free m bp bo Sep FP FO)as(mf & Free & Rest).
 exists mf;split;[rewrite elements_taptweak_eckey_blocks;rewrite eckey_tweak_blocks in Free;exact Free|exact Rest].
Qed.

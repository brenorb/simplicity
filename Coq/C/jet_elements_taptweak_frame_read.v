(** Reuse the actual byte/hash readers at arbitrary valid cursors in the
    linked Elements program, retaining the same final memory and frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_word_repr C.jet_read8s_layout C.jet_buffer_input C.jet_input_layout C.jet_frame_layout
 C.jet_sx_mem C.jet_secp_linkage C.jet_secp_frame C.jet_secp_hash_public_read
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require C.jets.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_read32s_layout C.jet_word32_chunks
 C.jet_uint32_array_init C.jet_sha_ctx8_model C.jet_sx_mem C.jet_secp_linkage
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require C.jets.

Require Import C.jet_secp_public_byte_read C.jet_secp_public_hash_read
 C.jet_secp_taptweak_io C.jet_secp_curve_statements C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_parse_start C.jet_transport.
From compcert Require Import Coqlib Globalenvs Maps Clightdefs.
Require Import C.jets_secp.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_curve_has_read8s:
 In(C.jets._read8s,C.jets.f_read8s)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)C.jets._read8s)elements_taptweak_curve_helpers=
 Some(C.jets._read8s,C.jets.f_read8s))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Lemma elements_taptweak_curve_has_read32s:
 In(C.jets._read32s,C.jets.f_read32s)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)C.jets._read32s)elements_taptweak_curve_helpers=
 Some(C.jets._read32s,C.jets.f_read32s))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque elements_taptweak_ge secp_ge.
Theorem eval_elements_taptweak_public_byte_read (xs:list (Ty.tySem (Word 3))) m bo bf bi edge cursor:
 Z.of_nat (length xs)<=Ptrofs.max_unsigned ->0<=cursor ->cursor+8*Z.of_nat (length xs)<=Int64.max_unsigned ->
 bo<>bf ->bf<>bi ->bo<>bi ->
 Mem.range_perm m bo 0 (Z.of_nat (length xs)) Cur Freeable ->Mem.range_perm m bf 0 16 Cur Freeable ->
 frame_fields_at m bf 0 bi edge cursor ->
 frame_input_cells_at m bi edge cursor (concat (map (@Translate.encode (Word 3)) xs)) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal C.jets.f_read8s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr (Z.of_nat (length xs)));Vptr bf Ptrofs.zero] E0 mf Vundef /\
 uint8_array_at mf bo 0 (map word8_array_value xs) /\
 frame_fields_at mf bf 0 bi edge (cursor+8*Z.of_nat (length xs)) /\
 keeps_permissions m mf /\lframe (fun b _=>b<>bf /\b<>bo) m mf /\readonly_preserved m mf.
Proof.
 intros Length Cursor Max OF FI OI Owned FreeFrame Source Input.
 destruct (eval_secp_public_byte_read xs m bo bf bi edge cursor Length Cursor Max OF FI OI Owned FreeFrame Source Input)as(mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_curve_has_read8s Call).
Qed.
Theorem eval_elements_taptweak_public_hash_read (h:Ty.tySem (Word 8)) m bo bf bi edge cursor:
 0<=cursor ->cursor+256<=Int64.max_unsigned ->bo<>bf ->bf<>bi ->bo<>bi ->
 Mem.range_perm m bo 0 32 Cur Freeable ->Mem.range_perm m bf 0 16 Cur Freeable ->
 frame_fields_at m bf 0 bi edge cursor ->frame_input_cells_at m bi edge cursor (Translate.encode h) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal C.jets.f_read32s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr 8);Vptr bf Ptrofs.zero] E0 mf Vundef /\
 uint32_array_at mf bo 0 (state_regs h) /\frame_fields_at mf bf 0 bi edge (cursor+256) /\
 keeps_permissions m mf /\lframe (fun b _=>b<>bf /\b<>bo) m mf /\readonly_preserved m mf.
Proof.
 intros Cursor Max OF FI OI FO FF Fields Input.
 destruct (eval_secp_public_hash_read h m bo bf bi edge cursor Cursor Max OF FI OI FO FF Fields Input)as(mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_curve_has_read32s Call).
Qed.
Lemma exec_elements_taptweak_key_read e le m mf bb bf:
 e!_read8s=None ->e!_buf=Some (bb,tarray tuchar 32) ->le!_src=Some (Vptr bf Ptrofs.zero) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal C.jets.f_read8s)
 [Vptr bb Ptrofs.zero;Vlong (Int64.repr 32);Vptr bf Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt elements_taptweak_ge e le m taptweak_key_read E0 le mf Out_normal.
Proof.
 intros Global Buf Source Read.
 destruct (elements_taptweak_curve_entries C.jets._read8s C.jets.f_read8s
 elements_taptweak_curve_has_read8s) as (b0 & b & S0 & F0 & Symbol & Function).
 unfold taptweak_key_read,curve_call;eapply exec_Scall with (vf:=Vptr b Ptrofs.zero)
 (f:=Internal C.jets.f_read8s) (vargs:=[Vptr bb Ptrofs.zero;Vlong (Int64.repr 32);Vptr bf Ptrofs.zero]) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   { eapply eval_Evar_global;[exact Global|exact Symbol]. }
   apply deref_loc_reference;reflexivity.
 - eapply eval_Econs.
   { eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]. }
   { reflexivity. }
   eapply eval_Econs;[constructor|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact Source|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Read.
Qed.

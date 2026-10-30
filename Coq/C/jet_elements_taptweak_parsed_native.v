(** Actual linked native suffix with parser-derived curve premises and startup preservation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_read8s_layout C.jet_toZ
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_secp_taptweak_native
 C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_result
 C.jet_secp_decompress_literal C.jet_secp_affine_word_valid C.jet_secp_curve_literal
 C.jet_secp_tweak_bytes_function C.jet_secp_xonly_tweak_function C.jet_secp_affine_storage
 C.jet_secp_taptweak_tag C.jet_secp_schnorr_startup C.jet_secp_linear_startup C.jet_secp_fe_math
 C.jet_secp_schnorr_challenge_hash C.jet_secp_word_bytes_codec C.jet_secp_root_chain_owned
 C.jet_secp_statement_prefix C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_taptweak_parsed_native C.jet_elements_taptweak_pure.
Require Import C.jet_elements_taptweak_native C.jet_elements_taptweak_runtime_ready.
Local Opaque secp_ge elements_taptweak_ge literal_decompress tweak_bytes_value tweak_bytes_result.
Theorem exec_elements_taptweak_parsed_native (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (ng pk:Ty.tySem (Word 8)) e le m bi bp bo bb:
 e!_input_pubkey=Some (bi,Tstruct __6478 noattr) ->e!_pubkey=Some (bp,Tstruct __2078 noattr) ->
 e!_output_pubkey=Some (bo,Tstruct __6478 noattr) ->e!_buf=Some (bb,tarray tuchar 32) ->
 e!_secp256k1_xonly_pubkey_tweak_add=None ->e!_secp256k1_xonly_pubkey_from_pubkey=None ->e!_secp256k1_xonly_pubkey_serialize=None ->
 NoDup [bi;bp;bo;bb] ->
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 xonly_parse_result pk=Int.one ->xonly_parsed_result pk m bi ->elements_taptweak_runtime_ready m ->
 uint8_array_at m bb 0 (schnorr_word_bytes ng) ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m (statement_sequence taptweak_native_statements Sskip) E0
 (taptweak_native_temps le (taptweak_result ng pk)) mf (taptweak_native_outcome (taptweak_result ng pk)) /\
 taptweak_native_bytes (taptweak_value ng pk) mf bb /\
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\b<>bo /\b<>bb) m mf /\mem_forward m mf /\elements_taptweak_runtime_ready mf /\readonly_preserved m mf.
Proof.
 intros InputKey PubKey OutputKey Buf TG CG SG Sep Owned Success Parsed Startup Bytes.
 destruct (proj1 (xonly_parse_success_iff pk) Success) as (Bound & ax & ay & Decoded).
 destruct (Parsed Bound ax ay Decoded) as (w & Stored & X & Y).
 pose proof (secp_decompress_curve pk (inl tt) (ax,ay) Decoded) as Curve.
 assert (BytesNative:uint8_array_at m bb 0 (map Int.repr (xonly_input_bytes ng))).
 { unfold xonly_input_bytes;rewrite word256_serializer_bytes;exact Bytes. }
 pose proof(proj1 Startup)as(Tables & Split & Beta & Modulus).
 destruct (exec_elements_taptweak_native Copy Clear Count ng ax ay w e le m bi bp bo bb
 InputKey PubKey OutputKey Buf TG CG SG Sep Owned Tables Split Beta Modulus Stored X Y Curve BytesNative) as
 (mf & Native & Value & OwnedF & Frame & Forward & ModulusF & Read).
 assert (Result:taptweak_result ng pk=tweak_bytes_result ng ax ay).
 { unfold taptweak_result;rewrite (proj2 (Z.ltb_lt _ _) Bound),Decoded;reflexivity. }
 assert (ValueEq:taptweak_value ng pk=tweak_bytes_value ng ax ay).
 { unfold taptweak_value;rewrite (proj2 (Z.ltb_lt _ _) Bound),Decoded;reflexivity. }
 assert (StartupF:elements_taptweak_runtime_ready mf).
 { eapply elements_taptweak_runtime_ready_owned with (slots:=[(bp,64);(bo,64);(bb,32)]);
 [exact Startup|exact Read| |].
 - intros b hi [Pair|[Pair|[Pair|[]]]];inversion Pair;subst;split;try (clear;lia);apply Owned;clear;cbn [In];tauto.
 - eapply lframe_implies;[exact Frame|intros b pos Outside Valid;clear -Outside;cbn [map fst In] in Outside;cbn;intuition congruence]. }
 exists mf;split.
 - rewrite Result;exact Native.
 - split;[rewrite ValueEq;exact Value|];split;[exact OwnedF|];split;[exact Frame|];split;[exact Forward|];split;[exact StartupF|exact Read].
Qed.

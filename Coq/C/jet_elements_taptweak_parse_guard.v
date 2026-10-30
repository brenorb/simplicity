(** Original TapTweak input-key parser and its early-return guard, both outcomes. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_word_repr C.jet_secp_fe_math C.jet_read8s_layout C.jet_sx_mem C.jet_memcpy_model C.jet_memset_model
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_bip0340_public_parse C.jet_secp_root_chain_owned C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_field
 C.jet_secp_xonly_parse_function C.jet_secp_decompress_literal C.jet_clight_internal_preserve.
Require Simplicity.Alg.
Require Import C.jet_secp_taptweak_parse C.jet_elements_taptweak_parser
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_parse_start C.jet_xonly_parse_control_at.
From compcert Require Import Globalenvs Coqlib.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_xonly_parse_lookup:
 secp_helper_lookup elements_taptweak_ge (_secp256k1_xonly_pubkey_parse,f_secp256k1_xonly_pubkey_parse)=
 Some(Internal f_secp256k1_xonly_pubkey_parse).
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.
Theorem exec_elements_taptweak_parse_guard (Copy:memcpy_model) (Clear:memset_model) pk e le m bkey bb:
 e!_input_pubkey=Some (bkey,Tstruct __6478 noattr) ->e!_buf=Some (bb,tarray tuchar 32) ->
 e!_secp256k1_xonly_pubkey_parse=None ->bkey<>bb ->
 Mem.range_perm m bkey 0 64 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 uint8_array_at m bb 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m taptweak_parse_guard E0
 (PTree.set _t'1 (Vint (xonly_parse_result pk)) le) mf (bip0340_parse_outcome pk) /\
 xonly_parsed_result pk mf bkey /\Mem.range_perm mf bkey 0 64 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bkey /\b<>bb) m mf /\readonly_preserved m mf.
Proof.
 intros Key Buf Symbol Separate FreeK FreeB Input.
 destruct (eval_elements_taptweak_xonly_pubkey_parse_owned Copy Clear pk m bkey bb Separate FreeK FreeB Input)
 as (mf & Parse & Parsed & KeyF & BufF & Frame & Read).
 assert (Call:Clight2.exec_stmt elements_taptweak_ge e le m taptweak_parse_call E0
  (PTree.set _t'1 (Vint (xonly_parse_result pk)) le) mf Out_normal).
 { destruct (secp_helper_lookup_exists elements_taptweak_ge _ _ elements_taptweak_xonly_parse_lookup) as (bf & Sym & Funct).
   unfold taptweak_parse_call;eapply exec_elements_taptweak_curve_call with (bf:=bf)
   (vargs:=[Vptr bkey Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vint (xonly_parse_result pk)).
   - exact Sym.
   - unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
   - exact Symbol.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Key|reflexivity|].
     eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|constructor].
   - exact Parse. }
 exists mf;split.
 - unfold taptweak_parse_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
   unfold bip0340_parse_outcome;destruct (xonly_parse_result_cases pk) as [Zero|One];rewrite Zero || rewrite One.
   + apply exec_elements_taptweak_xonly_guard_zero;apply PTree.gss.
   + apply exec_elements_taptweak_xonly_guard_one;apply PTree.gss.
 - split;[exact Parsed|];split;[exact KeyF|];split;[exact BufF|];split;assumption.
Qed.

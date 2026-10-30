(** Complete initialized Elements TapTweak implementation-to-Simplicity assertion contract. *)
From Coq Require Import ZArith.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Simplicity.Alg.
Require Import C.jets_secp C.jet_secp_linkage C.jet_readBit_layout C.jet_sx_mem
 C.jet_frame_spec C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_partial
 C.jet_secp_initialized_partial_contract C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model
 C.jet_secp_taptweak_tag C.jet_secp_taptweak_writer_state C.jet_secp_taptweak_hash
 C.jet_secp_taptweak_parsed_native C.jet_secp_taptweak_finish C.jet_secp_taptweak_public_function C.jet_secp_taptweak_literal.
Require C.jets_elements.
Require Import C.jet_elements_taptweak_program C.jet_elements_taptweak_pure C.jet_elements_taptweak_tag
 C.jet_elements_taptweak_message_hash C.jet_elements_taptweak_tag_startup.
Require Import C.jet_initialized_partial_contract_at C.jet_taptweak_literal_at
 C.jet_elements_taptweak_public_function C.jet_elements_taptweak_runtime_ready.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque elements_taptweak_ge taptweak_value taptweak_result elements_taptweak_hash_word.
Theorem elements_build_taptweak_initialized_local_spec :
 memcpy_model ->memset_model ->ctz_model ->
 jet_initialized_partial_local_spec_at elements_taptweak_ge elements_taptweak_runtime_ready C.jets_elements.f_simplicity_build_taptweak
 (Word 9) (Word 8) (@literal_taptweak_at elements_taptweak_iv_word (Alg.AssertionSem option_Monad_Zero)).
Proof.
 intros Copy Clear Count env m bd base bs sbase bi bw edge outedge cursor rc value
 Ready Base Align Source RC Max Input Output.
 destruct value as [pk h].
 change (rc+512<=Int64.max_unsigned) in Max.
 change (write_frame_at m bd base bw outedge cursor 256) in Output.
 destruct (eval_elements_taptweak_public Copy Clear Count pk h env m bd base bs sbase bi bw edge outedge rc cursor
 Ready Base Align Source RC Max Input Output) as (mf & Call & Observe & Loads & Forward & ReadyF).
 assert (Return:Vint (bit_int (taptweak_result (elements_taptweak_hash_word pk h) pk))=
 jet_partial_return (taptweak_output (elements_taptweak_hash_word pk h) pk)).
 { rewrite taptweak_result_option;unfold taptweak_output.
 destruct (taptweak_value (elements_taptweak_hash_word pk h) pk);reflexivity. }
 exists mf;rewrite literal_taptweak_matches_output_at;
 change (tagged_taptweak_hash_word elements_taptweak_iv_word pk h) with (elements_taptweak_hash_word pk h);split.
 - rewrite <-Return;exact Call.
 - split;[exact Observe|];split;[exact Loads|exact ReadyF].
Qed.

Theorem elements_taptweak_initialized_memory_exists:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\elements_taptweak_runtime_ready m.
Proof.
 destruct elements_taptweak_tag_startup_exists as(m & Init & Rest).
 exists m;split;[exact Init|apply elements_taptweak_runtime_ready_initial;exact Init].
Qed.

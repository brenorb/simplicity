(** Shared generic TapTweak sequence recombination at any global environment. *)
From Coq Require Import List.
From compcert Require Import Clight ClightBigstep Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_statement_prefix C.jet_secp_root_chain_owned
 C.jet_secp_sha_init_copy C.jet_secp_taptweak_tag_exec C.jet_secp_taptweak_prefix
 C.jet_secp_taptweak_body_prefix C.jet_secp_taptweak_io C.jet_secp_taptweak_key_phase
 C.jet_secp_public_hash_read C.jet_secp_taptweak_hash C.jet_secp_taptweak_hash_phase C.jet_secp_taptweak_parse.
Import ListNotations.
Set Default Timeout 10.
Require Import C.jet_secp_taptweak_phase_glue.
Section Phases.
Variable ge:Clight.genv.
Lemma exec_taptweak_initial_then_at e le m mi lef mf out:
 Clight2.exec_stmt ge e le m taptweak_initial_phase E0 le mi Out_normal ->
 Clight2.exec_stmt ge e le mi (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out ->
 Clight2.exec_stmt ge e le m (fn_body f_simplicity_generic_taptweak) E0 lef mf out.
Proof.
 intros Initial Rest;rewrite taptweak_prefix_source.
 eapply exec_sequence_prefix_then_suffix with
 (prefix:=[taptweak_tag_stmt;sha_init_copy_stmt __res _ctx__1 _output_hash;taptweak_prefix_hash])
 (last:=taptweak_prefix_hash);[exact Initial|exact Rest].
Qed.
Lemma exec_taptweak_key_then_at e le m mi le1 lef mf out:
 Clight2.exec_stmt ge e le m taptweak_key_phase E0 le1 mi Out_normal ->
 Clight2.exec_stmt ge e le1 mi (root_drop_statements 7 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out ->
 Clight2.exec_stmt ge e le m (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out.
Proof.
 intros Key Rest;rewrite taptweak_key_phase_source.
 eapply exec_sequence_prefix_then_suffix with (prefix:=[taptweak_key_read;taptweak_key_absorb])
 (last:=taptweak_parse_guard);[exact Key|exact Rest].
Qed.
Lemma exec_taptweak_key_aborts_at e le m lef mf out:
 out<>Out_normal ->Clight2.exec_stmt ge e le m taptweak_key_phase E0 lef mf out ->
 Clight2.exec_stmt ge e le m (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out.
Proof.
 intros Abnormal Key;rewrite taptweak_key_phase_source.
 eapply exec_sequence_prefix_aborts with (prefix:=[taptweak_key_read;taptweak_key_absorb])
 (last:=taptweak_parse_guard);[exact Abnormal|exact Key].
Qed.
Lemma exec_taptweak_hash_then_at e le m mi lef mf out:
 Clight2.exec_stmt ge e le m taptweak_hash_phase E0 le mi Out_normal ->
 Clight2.exec_stmt ge e le mi (root_drop_statements 11 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out ->
 Clight2.exec_stmt ge e le m (root_drop_statements 7 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out.
Proof.
 intros Hash Rest;rewrite taptweak_hash_read_source,taptweak_message_hash_source.
 eapply exec_sequence_prefix_then_suffix with (prefix:=[secp_local_hash_read _input_hash;taptweak_message_absorb;taptweak_message_finalize])
 (last:=taptweak_message_digest);[exact Hash|exact Rest].
Qed.
End Phases.

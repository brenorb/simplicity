(** Recombine the checked phases at the original generic function's sequence boundaries. *)
From Coq Require Import List.
From compcert Require Import Clight ClightBigstep Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_statement_prefix C.jet_secp_root_chain_owned
 C.jet_secp_sha_init_copy C.jet_secp_taptweak_tag_exec C.jet_secp_taptweak_prefix
 C.jet_secp_taptweak_body_prefix C.jet_secp_taptweak_io C.jet_secp_taptweak_key_phase
 C.jet_secp_public_hash_read C.jet_secp_taptweak_hash C.jet_secp_taptweak_hash_phase C.jet_secp_taptweak_parse.
Import ListNotations.
Set Default Timeout 10.
Lemma exec_sequence_prefix_then_suffix ge e prefix last suffix le m le1 m1 le2 m2 out:
 Clight2.exec_stmt ge e le m (statement_sequence prefix last) E0 le1 m1 Out_normal ->
 Clight2.exec_stmt ge e le1 m1 suffix E0 le2 m2 out ->
 Clight2.exec_stmt ge e le m (statement_sequence prefix (Ssequence last suffix)) E0 le2 m2 out.
Proof.
 revert le m le1 m1;induction prefix as [|head tail IH];intros le m le1 m1 Prefix Suffix;cbn [statement_sequence] in *.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prefix|exact Suffix].
 - inversion Prefix;subst.
   + match goal with
     | H:?t1 ** ?t2=E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->]
     | H:E0=?t1 ** ?t2 |- _=>destruct (Eapp_E0_inv t1 t2 (eq_sym H)) as [-> ->] end.
     change E0 with (E0 ** E0);eapply exec_Sseq_1;[eassumption|eapply IH;eassumption].
   + contradiction.
Qed.
Lemma exec_sequence_prefix_aborts ge e prefix last suffix le m lef mf out:
 out<>Out_normal ->Clight2.exec_stmt ge e le m (statement_sequence prefix last) E0 lef mf out ->
 Clight2.exec_stmt ge e le m (statement_sequence prefix (Ssequence last suffix)) E0 lef mf out.
Proof.
 intro Abnormal;revert le m;induction prefix as [|head tail IH];intros le m Prefix;cbn [statement_sequence] in *.
 - eapply exec_Sseq_2;[exact Prefix|exact Abnormal].
 - inversion Prefix;subst.
   + match goal with
     | H:?t1 ** ?t2=E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->]
     | H:E0=?t1 ** ?t2 |- _=>destruct (Eapp_E0_inv t1 t2 (eq_sym H)) as [-> ->] end.
     change E0 with (E0 ** E0);eapply exec_Sseq_1;[eassumption|eapply IH;eassumption].
   + eapply exec_Sseq_2;eassumption.
Qed.
Local Opaque secp_ge.
Lemma exec_taptweak_initial_then e le m mi lef mf out:
 Clight2.exec_stmt secp_ge e le m taptweak_initial_phase E0 le mi Out_normal ->
 Clight2.exec_stmt secp_ge e le mi (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out ->
 Clight2.exec_stmt secp_ge e le m (fn_body f_simplicity_generic_taptweak) E0 lef mf out.
Proof.
 intros Initial Rest;rewrite taptweak_prefix_source.
 eapply exec_sequence_prefix_then_suffix with
 (prefix:=[taptweak_tag_stmt;sha_init_copy_stmt __res _ctx__1 _output_hash;taptweak_prefix_hash])
 (last:=taptweak_prefix_hash);[exact Initial|exact Rest].
Qed.
Lemma exec_taptweak_key_then e le m mi le1 lef mf out:
 Clight2.exec_stmt secp_ge e le m taptweak_key_phase E0 le1 mi Out_normal ->
 Clight2.exec_stmt secp_ge e le1 mi (root_drop_statements 7 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out ->
 Clight2.exec_stmt secp_ge e le m (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out.
Proof.
 intros Key Rest;rewrite taptweak_key_phase_source.
 eapply exec_sequence_prefix_then_suffix with (prefix:=[taptweak_key_read;taptweak_key_absorb])
 (last:=taptweak_parse_guard);[exact Key|exact Rest].
Qed.
Lemma exec_taptweak_key_aborts e le m lef mf out:
 out<>Out_normal ->Clight2.exec_stmt secp_ge e le m taptweak_key_phase E0 lef mf out ->
 Clight2.exec_stmt secp_ge e le m (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out.
Proof.
 intros Abnormal Key;rewrite taptweak_key_phase_source.
 eapply exec_sequence_prefix_aborts with (prefix:=[taptweak_key_read;taptweak_key_absorb])
 (last:=taptweak_parse_guard);[exact Abnormal|exact Key].
Qed.
Lemma exec_taptweak_hash_then e le m mi lef mf out:
 Clight2.exec_stmt secp_ge e le m taptweak_hash_phase E0 le mi Out_normal ->
 Clight2.exec_stmt secp_ge e le mi (root_drop_statements 11 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out ->
 Clight2.exec_stmt secp_ge e le m (root_drop_statements 7 (fn_body f_simplicity_generic_taptweak)) E0 lef mf out.
Proof.
 intros Hash Rest;rewrite taptweak_hash_read_source,taptweak_message_hash_source.
 eapply exec_sequence_prefix_then_suffix with (prefix:=[secp_local_hash_read _input_hash;taptweak_message_absorb;taptweak_message_finalize])
 (last:=taptweak_message_digest);[exact Hash|exact Rest].
Qed.

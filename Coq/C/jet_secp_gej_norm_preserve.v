(** Startup-state preservation for the actual normalization reader/tag and
    skip path, without external-call properties or input/global separation. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep Maps Integers Values Memory Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_field_io_preserve C.jet_secp_frame_preserve
 C.jet_secp_modinfo_fe_caller C.jet_secp_gej_predicate_body C.jet_secp_gej_norm_branch
 C.jet_secp_affine_skip C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Require C.jets.
Import ListNotations.
Set Default Timeout 10.

Lemma secp_skipBits_link :
 Genv.find_symbol secp_ge C.jets._skipBits=Some(secp_symbol_block C.jets._skipBits) /\
 Genv.find_funct secp_ge(Vptr(secp_symbol_block C.jets._skipBits)Ptrofs.zero)=Some(Internal C.jets.f_skipBits).
Proof. split;reflexivity. Qed.
Lemma secp_skip_fe_link : Genv.find_symbol secp_ge _skip_fe=Some(secp_symbol_block _skip_fe) /\
 Genv.find_funct secp_ge(Vptr(secp_symbol_block _skip_fe)Ptrofs.zero)=Some(Internal f_skip_fe).
Proof. split;reflexivity. Qed.
Lemma secp_writeBit_link : Genv.find_symbol secp_ge _writeBit=Some(secp_symbol_block _writeBit) /\
 Genv.find_funct secp_ge(Vptr(secp_symbol_block _writeBit)Ptrofs.zero)=Some(Internal C.jets.f_writeBit).
Proof. split;reflexivity. Qed.
Local Opaque secp_ge.

Theorem secp_skip_fe_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_skip_fe)args t mf result -> readonly_preserved m mf.
Proof.
 apply function_preserved_from_body;[|reflexivity].
 intros e le mi tr lef mo out Run Plain.
 change(Clight2.exec_stmt secp_ge e le mi
  (Scall None(Evar C.jets._skipBits(type_of_function C.jets.f_skipBits))
   [Etempvar _dst(tptr(Tstruct _frameItem noattr));Econst_int(Int.repr 256)tint])tr lef mo out) in Run.
 eapply named_call_preserved;[exact Plain|exact(proj1 secp_skipBits_link)|exact(proj2 secp_skipBits_link)|
  exact secp_skipBits_preserved|exact Run].
Qed.

Theorem secp_skip_ge_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_skip_ge)args t mf result -> readonly_preserved m mf.
Proof.
 apply function_preserved_from_body;[|reflexivity].
 intros e le mi tr lef mo out Run Plain;rewrite affine_skip_ge_source in Run.
 eapply sequence_preserved;[| |exact Run].
 all:intros le0 m0 t0 lef0 mf0 out0 Sub;unfold affine_skip_fe_stmt in Sub;
  eapply named_call_preserved;[exact Plain|exact(proj1 secp_skip_fe_link)|exact(proj2 secp_skip_fe_link)|
   exact secp_skip_fe_preserved|exact Sub].
Qed.

Lemma gej_norm_read_closed : closed_stmtb gej_reader_internal_table gej_predicate_read_stmt=true.
Proof. vm_compute;reflexivity. Qed.
Lemma gej_norm_flag_closed : closed_stmtb field_io_helpers gej_predicate_flag_stmt=true.
Proof. vm_compute;reflexivity. Qed.

Theorem gej_norm_header_preserved e le m t lef mf out : plain_env e ->
 Clight2.exec_stmt secp_ge e le m gej_norm_header t lef mf out -> readonly_preserved m mf.
Proof.
 intros Plain Run;unfold gej_norm_header in Run;eapply sequence_preserved;[| |exact Run].
 - intros;eapply(proj1(internal_exec_preserved _ _ field_io_helpers_ok));eauto using gej_norm_flag_closed.
 - intros le0 m0 t0 lef0 mf0 out0 Sub;unfold gej_norm_tag_stmt in Sub.
   eapply named_call_preserved;[exact Plain|exact(proj1 secp_writeBit_link)|exact(proj2 secp_writeBit_link)|
    exact secp_writeBit_preserved|exact Sub].
Qed.

Theorem gej_norm_read_tag_preserved e le m t lef mf out : plain_env e ->
 Clight2.exec_stmt secp_ge e le m(Ssequence gej_predicate_read_stmt gej_norm_header)t lef mf out ->
 readonly_preserved m mf.
Proof.
 intros Plain Run;eapply sequence_preserved;[| |exact Run].
 - intros;eapply(proj1(internal_exec_preserved _ _ gej_reader_internal_table_correct));
    eauto using gej_norm_read_closed.
 - intros;eapply gej_norm_header_preserved;eassumption.
Qed.

(** Scalar split constants at their actual addresses in the Elements link.
    Readiness follows from the unchanged initializers, not source-unit blocks. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory Globalenvs Ctypes Clight.
Require Import C.jets_secp C.jet_elements_taptweak_program C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_globals C.jet_elements_taptweak_startup
 C.jet_secp_scalar_constant C.jet_secp_split_multipliers C.jet_secp_split_constants
 C.jet_secp_scalar_lambda_global C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_mul_writer_bridge
 C.jet_secp_scalar_mul512_accumulate C.jet_clight_internal_preserve.
Require Import C.jet_scalar_constant_init.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_multiplier_block first:=elements_taptweak_symbol_block(split_multiplier_id first).
Definition elements_taptweak_basis_block first:=elements_taptweak_symbol_block(split_basis_id first).
Definition elements_taptweak_lambda_block:=elements_taptweak_symbol_block _secp256k1_const_lambda.
Definition elements_taptweak_multipliers_ready m:=forall first,
 scalar_constant_state(elements_taptweak_multiplier_block first)(split_multiplier_words first)m.
Definition elements_taptweak_split_ready m:=elements_taptweak_multipliers_ready m /\
 (forall first,scalar_constant_state(elements_taptweak_basis_block first)(split_basis_words first)m) /\
 scalar_constant_state elements_taptweak_lambda_block scalar_lambda_words m.
Lemma elements_taptweak_multiplier_symbol first:
 Genv.find_symbol elements_taptweak_ge(split_multiplier_id first)=Some(elements_taptweak_multiplier_block first).
Proof. destruct first;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_multiplier_info first:
 Genv.find_var_info(Genv.globalenv elements_taptweak_linked_program)(elements_taptweak_multiplier_block first)=
 Some(split_multiplier_var first).
Proof. destruct first;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_basis_symbol first:
 Genv.find_symbol elements_taptweak_ge(split_basis_id first)=Some(elements_taptweak_basis_block first).
Proof. destruct first;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_basis_info first:
 Genv.find_var_info(Genv.globalenv elements_taptweak_linked_program)(elements_taptweak_basis_block first)=
 Some(split_basis_var first).
Proof. destruct first;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_lambda_symbol:
 Genv.find_symbol elements_taptweak_ge _secp256k1_const_lambda=Some elements_taptweak_lambda_block.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_lambda_info:
 Genv.find_var_info(Genv.globalenv elements_taptweak_linked_program)elements_taptweak_lambda_block=
 Some v_secp256k1_const_lambda.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge elements_taptweak_linked_program
 elements_taptweak_multiplier_block elements_taptweak_basis_block elements_taptweak_lambda_block.
Theorem elements_taptweak_multipliers_initializes m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_multipliers_ready m.
Proof.
 intros Init first;apply(scalar_constant_initializes_at elements_taptweak_linked_program(split_multiplier_var first));
 [apply elements_taptweak_multiplier_info|apply split_multiplier_count|destruct first;reflexivity|
 destruct first;reflexivity|destruct first;reflexivity|exact Init].
Qed.
Theorem elements_taptweak_split_initializes m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_split_ready m.
Proof.
 intro Init;split;[apply elements_taptweak_multipliers_initializes;exact Init|];split.
 - intro first;apply(scalar_constant_initializes_at elements_taptweak_linked_program(split_basis_var first));
   [apply elements_taptweak_basis_info|apply split_basis_count|destruct first;reflexivity|
   destruct first;reflexivity|destruct first;reflexivity|exact Init].
 - apply(scalar_constant_initializes_at elements_taptweak_linked_program v_secp256k1_const_lambda);
   [apply elements_taptweak_lambda_info|apply scalar_lambda_words_count|reflexivity|reflexivity|reflexivity|exact Init].
Qed.
Theorem elements_taptweak_split_initial_memory:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\elements_taptweak_split_ready m.
Proof.
 destruct elements_taptweak_initial_memory_exists as(m & Init);exists m;split;
 [exact Init|apply elements_taptweak_split_initializes;exact Init].
Qed.
Lemma elements_taptweak_multipliers_readonly m mf:
 elements_taptweak_multipliers_ready m ->readonly_preserved m mf ->elements_taptweak_multipliers_ready mf.
Proof. intros Ready Preserve first;eapply scalar_constant_readonly;[apply Ready|exact Preserve]. Qed.
Lemma elements_taptweak_split_readonly m mf:
 elements_taptweak_split_ready m ->readonly_preserved m mf ->elements_taptweak_split_ready mf.
Proof.
 intros [Multipliers [Basis Lambda]] Preserve;split.
 - eapply elements_taptweak_multipliers_readonly;[exact Multipliers|exact Preserve].
 - split;[intro first;eapply scalar_constant_readonly;[apply Basis|exact Preserve]|
 eapply scalar_constant_readonly;[exact Lambda|exact Preserve]].
Qed.
Lemma elements_taptweak_basis_storage first m:elements_taptweak_split_ready m ->
 scalar_at m(elements_taptweak_basis_block first)0(map Int64.repr(scalar_limbs_of(split_basis_value first))).
Proof.
 intros [_ [Basis _]];rewrite <-(split_basis_value_checked first),four_words_scalar_limbs by apply split_basis_count.
 exact(proj1(Basis first)).
Qed.
Lemma elements_taptweak_lambda_storage m:elements_taptweak_split_ready m ->
 scalar_at m elements_taptweak_lambda_block 0(map Int64.repr(scalar_limbs_of canonical_lambda_value)).
Proof.
 intros [_ [_ Lambda]];rewrite <-scalar_lambda_words_value,four_words_scalar_limbs by apply scalar_lambda_words_count.
 exact(proj1 Lambda).
Qed.
Lemma elements_taptweak_basis_separate first m b:elements_taptweak_split_ready m ->
 Mem.range_perm m b 0 32 Cur Freeable ->b<>elements_taptweak_basis_block first.
Proof. intros [_ [Basis _]] Free;eapply scalar_constant_separate;[apply Basis|exact Free]. Qed.
Lemma elements_taptweak_lambda_separate m b:elements_taptweak_split_ready m ->
 Mem.range_perm m b 0 32 Cur Freeable ->b<>elements_taptweak_lambda_block.
Proof. intros [_ [_ Lambda]] Free;eapply scalar_constant_separate;[exact Lambda|exact Free]. Qed.

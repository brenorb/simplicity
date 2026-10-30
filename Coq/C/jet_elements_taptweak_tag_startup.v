(** The real Elements tag in the linked artifact, with no caller-supplied tag
    bytes or separation needed at initialization. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Ctypes Clight Memory Globalenvs.
Require Import C.jets_elements C.jet_elements_taptweak_program C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_globals.
Require Import C.jet_elements_taptweak_tag_state_at.
Set Default Timeout 10.
Definition elements_taptweak_linked_tag_block:=elements_taptweak_symbol_block jets_elements._taptweak.
Definition elements_taptweak_linked_tag_state:=elements_taptweak_tag_state_at elements_taptweak_linked_tag_block.
Lemma elements_taptweak_linked_tag_info:
 Genv.find_var_info (Genv.globalenv elements_taptweak_linked_program)
 elements_taptweak_linked_tag_block=Some jets_elements.v_taptweak.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_linked_tag_symbol:
 Genv.find_symbol elements_taptweak_ge jets_elements._taptweak=Some elements_taptweak_linked_tag_block.
Proof. vm_compute;reflexivity. Qed.
Theorem elements_taptweak_linked_tag_initial m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_linked_tag_state m.
Proof. exact (elements_taptweak_tag_initial_at _ _ m elements_taptweak_linked_tag_info). Qed.
Theorem elements_taptweak_tag_startup_exists:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\
 elements_taptweak_sha_startup m /\elements_taptweak_linked_tag_state m.
Proof.
 destruct elements_taptweak_sha_startup_exists as (m & Init & Sha).
 exists m;split;[exact Init|];split;[exact Sha|exact (elements_taptweak_linked_tag_initial m Init)].
Qed.
Definition elements_taptweak_linked_tag_owned_separate:=elements_taptweak_tag_owned_separate_at elements_taptweak_linked_tag_block.
Definition elements_taptweak_linked_tag_output_separate:=elements_taptweak_tag_output_separate_at elements_taptweak_linked_tag_block.
Definition elements_taptweak_linked_tag_framed:=elements_taptweak_tag_framed_at elements_taptweak_linked_tag_block.
Definition elements_taptweak_linked_tag_after_write:=elements_taptweak_tag_after_write_at elements_taptweak_linked_tag_block.

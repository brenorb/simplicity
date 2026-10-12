(** The Elements current-input jets run on fresh frames from any represented
    environment (continuation of [jet_elements_executable_conf]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_uint32_array_init.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_elements_prim.
Require Import C.jet_elements_indexed_ptr C.jet_elements_indexed_ptr_jets C.jet_elements_input_hash_jets.
Require Import C.jet_elements_hash_elem C.jet_elements_executable C.jet_elements_executable_conf.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Require Import C.jet_elements_current_ptr_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_current_gen C.jet_elements_current_gen_jets C.jet_elements_current_jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma current_ptr_rep_stable {X} (elems_of : Elements.env -> list X) ix_of elemrep sz poff adelta cdelta :
  elem_stable elemrep ->
  env_rep_sep_stable (current_ptr_rep elems_of ix_of elemrep sz poff adelta cdelta).
Proof. intros HS m m' env e fp HE H. unfold current_ptr_rep in *. rep_stable_with HE H. Qed.

Lemma current_gen_rep_stable {X} (elems_of : Elements.env -> list X) elemrep sz adelta cdelta :
  elem_stable elemrep ->
  env_rep_sep_stable (current_gen_rep elems_of elemrep sz adelta cdelta).
Proof. intros HS m m' env e fp HE H. unfold current_gen_rep in *. rep_stable_with HE H. Qed.

Lemma current_scalar_rep_stable {X} (elems_of : Elements.env -> list X) valz sz voff adelta cdelta :
  env_rep_stable (current_scalar_rep elems_of valz sz voff adelta cdelta).
Proof. intros m m' env e HE H. unfold current_scalar_rep in *. rep_stable_with HE H. Qed.

Lemma input_amount_elem_rep_stable : elem_stable input_amount_elem_rep.
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply asset_rep_stable; eassumption.
  - eapply amount_rep_stable; eassumption.
Qed.

Lemma flag_hash_rep_stable g foff hoff : elem_stable (flag_hash_rep g foff hoff).
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros h Hh. eapply hash_elem_rep_stable; [exact HE|exact (H2 h Hh)].
Qed.

Local Ltac bound := vm_compute; discriminate.
Local Ltac runs_type T :=
  lazymatch T with
  | application_jet_local_spec ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_runs_on_fresh_frames f ge E A B r s)
  | application_jet_local_spec_sep ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_sep_runs_on_fresh_frames f ge E A B r s)
  end.
Local Tactic Notation "run" constr(H) tactic(S) :=
  eapply application_jet_local_spec_sep_executable; [bound|bound|exact H|S].

Theorem elements_current_prev_outpoint_local_spec_executable :
  ltac:(let T := type of elements_current_prev_outpoint_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_prev_outpoint_local_spec (apply current_ptr_rep_stable; exact outpoint_rep_stable). Qed.

Theorem elements_current_asset_local_spec_executable :
  ltac:(let T := type of elements_current_asset_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_asset_local_spec (apply current_ptr_rep_stable; exact input_asset_elem_stable). Qed.

Theorem elements_current_script_hash_local_spec_executable :
  ltac:(let T := type of elements_current_script_hash_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_script_hash_local_spec (apply current_ptr_rep_stable; exact (uint32_elem_stable utxo_script_hash_words)). Qed.

Theorem elements_current_script_sig_hash_local_spec_executable :
  ltac:(let T := type of elements_current_script_sig_hash_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_script_sig_hash_local_spec (apply current_ptr_rep_stable; exact (uint32_elem_stable script_sig_hash_words)). Qed.

Theorem elements_current_issuance_asset_proof_local_spec_executable :
  ltac:(let T := type of elements_current_issuance_asset_proof_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_issuance_asset_proof_local_spec (apply current_ptr_rep_stable; exact (uint32_elem_stable issuance_asset_proof_words)). Qed.

Theorem elements_current_issuance_token_proof_local_spec_executable :
  ltac:(let T := type of elements_current_issuance_token_proof_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_issuance_token_proof_local_spec (apply current_ptr_rep_stable; exact (uint32_elem_stable issuance_token_proof_words)). Qed.

Theorem elements_current_reissuance_blinding_local_spec_executable :
  ltac:(let T := type of elements_current_reissuance_blinding_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_reissuance_blinding_local_spec (apply current_ptr_rep_stable; exact (issuance_hash_elem_stable 0 gh_blinding)). Qed.

Theorem elements_current_new_issuance_contract_local_spec_executable :
  ltac:(let T := type of elements_current_new_issuance_contract_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_new_issuance_contract_local_spec (apply current_ptr_rep_stable; exact (issuance_hash_elem_stable 0 gh_contract)). Qed.

Theorem elements_current_reissuance_entropy_local_spec_executable :
  ltac:(let T := type of elements_current_reissuance_entropy_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_reissuance_entropy_local_spec (apply current_ptr_rep_stable; exact (issuance_hash_elem_stable 72 gh_entropy)). Qed.

Theorem elements_current_issuance_asset_amount_local_spec_executable :
  ltac:(let T := type of elements_current_issuance_asset_amount_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_issuance_asset_amount_local_spec (apply current_ptr_rep_stable; exact issuance_amount_elem_stable). Qed.

Theorem elements_current_amount_local_spec_executable :
  ltac:(let T := type of elements_current_amount_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_amount_local_spec (apply current_gen_rep_stable; exact input_amount_elem_rep_stable). Qed.

Theorem elements_current_pegin_local_spec_executable :
  ltac:(let T := type of elements_current_pegin_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_pegin_local_spec (apply current_gen_rep_stable; exact (flag_hash_rep_stable sigTxiPegin 537 32)). Qed.

Theorem elements_current_annex_hash_local_spec_executable :
  ltac:(let T := type of elements_current_annex_hash_local_spec in let R := runs_type T in exact R).
Proof. run elements_current_annex_hash_local_spec (apply current_gen_rep_stable; exact (flag_hash_rep_stable annex_hash_of 536 0)). Qed.

Theorem elements_current_sequence_local_spec_executable :
  ltac:(let T := type of elements_current_sequence_local_spec in let R := runs_type T in exact R).
Proof.
  eapply application_jet_local_spec_executable;
    [bound|bound|exact elements_current_sequence_local_spec|apply current_scalar_rep_stable].
Qed.

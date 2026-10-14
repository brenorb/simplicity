(** The proved Elements jets run on fresh frames from any represented
    environment.

    As for the Bitcoin unit ([jet_env_rep_stable], [jet_app_executable_registry]):
    every Elements environment relation observes the C environment only
    through successful loads, hence is stable under [memory_extension]; with
    the constructibility of the frame premises each proved Elements jet runs,
    for every input, from any memory in which its relation holds (and whose
    footprint blocks exist) and leaves the canonical result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_uint32_array_init.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_elements_prim.
Require Import C.jet_elements_hash_elem C.jet_elements_hash_getter_local.
Require Import C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr C.jet_elements_indexed_ptr_jets.
Require C.jet_elements_version_local C.jet_elements_locktime_local C.jet_elements_current_index_local.
Require C.jet_elements_script_cmr_local C.jet_elements_hash_field_jets C.jet_elements_genesis_hash_local.
Require C.jet_elements_tapleaf_version_local C.jet_elements_tappath_local.
Require C.jet_elements_indexed_scalar_jets C.jet_elements_input_hash_jets C.jet_elements_output_proof_jets.
Require C.jet_elements_annex_local C.jet_elements_pegin_local.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma uint32_array_at_ext m m' b base xs :
  memory_extension m m' -> uint32_array_at m b base xs -> uint32_array_at m' b base xs.
Proof.
  intros HE H i x Hx. eapply memory_extension_load; [exact HE|exact (H i x Hx)].
Qed.

Definition elem_stable {X : Type} (elemrep : mem -> block -> Z -> X -> Prop) : Prop :=
  forall m m' b ofs x, memory_extension m m' -> elemrep m b ofs x -> elemrep m' b ofs x.

Lemma hash_elem_rep_stable : elem_stable hash_elem_rep.
Proof.
  intros m m' b ofs h HE H. unfold hash_elem_rep in *. eapply uint32_array_at_ext; eassumption.
Qed.

Lemma outpoint_rep_stable : elem_stable outpoint_rep.
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply uint32_array_at_ext; eassumption.
  - eapply memory_extension_load; eassumption.
Qed.

Lemma annex_elem_rep_stable : elem_stable jet_elements_annex_local.annex_elem_rep.
Proof.
  intros m m' b ofs o HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros h Hh. eapply hash_elem_rep_stable; [exact HE|exact (H2 h Hh)].
Qed.

Lemma pegin_elem_rep_stable : elem_stable jet_elements_pegin_local.pegin_elem_rep.
Proof.
  intros m m' b ofs o HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros h Hh. eapply hash_elem_rep_stable; [exact HE|exact (H2 h Hh)].
Qed.

Lemma uint32_elem_stable {X : Type} (words : X -> list int) :
  elem_stable (fun m b ofs x => uint32_array_at m b ofs (words x)).
Proof. intros m m' b ofs x HE H. eapply uint32_array_at_ext; eassumption. Qed.

Ltac ext_fact HE :=
  first
  [ eassumption
  | eapply (memory_extension_load _ _ _ _ _ _ HE); eassumption
  | eapply (uint32_array_at_ext _ _ _ _ _ HE); eassumption
  | (intros; eapply (memory_extension_load _ _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (uint32_array_at_ext _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (hash_elem_rep_stable _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (annex_elem_rep_stable _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (pegin_elem_rep_stable _ _ _ _ _ HE); eauto; fail)
  | (intros; match goal with HS : elem_stable _ |- _ => eapply (HS _ _ _ _ _ HE); eauto end; fail) ].

Ltac rep_stable_with HE H :=
  repeat match type of H with
  | exists _, _ => let x := fresh "x" in destruct H as [x H]; exists x
  end;
  repeat match goal with
  | H0 : _ /\ _ |- _ => destruct H0
  end;
  repeat split; ext_fact HE.

Lemma version_rep_stable : env_rep_stable jet_elements_version_local.elements_version_env_rep.
Proof. intros m m' env e HE H. unfold jet_elements_version_local.elements_version_env_rep in *. rep_stable_with HE H. Qed.

Lemma locktime_rep_stable : env_rep_stable jet_elements_locktime_local.elements_locktime_env_rep.
Proof. intros m m' env e HE H. unfold jet_elements_locktime_local.elements_locktime_env_rep in *. rep_stable_with HE H. Qed.

Lemma current_index_rep_stable :
  env_rep_stable jet_elements_current_index_local.elements_current_index_env_rep.
Proof. intros m m' env e HE H. unfold jet_elements_current_index_local.elements_current_index_env_rep in *. rep_stable_with HE H. Qed.

Lemma script_cmr_rep_stable :
  env_rep_sep_stable jet_elements_script_cmr_local.elements_script_cmr_env_rep.
Proof. intros m m' env e fp HE H. unfold jet_elements_script_cmr_local.elements_script_cmr_env_rep in *. rep_stable_with HE H. Qed.

Lemma genesis_rep_stable :
  env_rep_sep_stable jet_elements_genesis_hash_local.elements_genesis_hash_env_rep.
Proof. intros m m' env e fp HE H. unfold jet_elements_genesis_hash_local.elements_genesis_hash_env_rep in *. rep_stable_with HE H. Qed.

Lemma hash_getter_rep_stable {E : Set} (hash_of : E -> _) pdelta hdelta psz :
  env_rep_sep_stable (hash_getter_rep hash_of pdelta hdelta psz).
Proof. intros m m' env e fp HE H. unfold hash_getter_rep in *. rep_stable_with HE H. Qed.

Lemma tapleaf_version_rep_stable :
  env_rep_sep_stable jet_elements_tapleaf_version_local.elements_tapleaf_version_env_rep.
Proof. intros m m' env e fp HE H. unfold jet_elements_tapleaf_version_local.elements_tapleaf_version_env_rep in *. rep_stable_with HE H. Qed.

Lemma tappath_rep_stable :
  env_rep_sep_stable jet_elements_tappath_local.elements_tappath_env_rep.
Proof. intros m m' env e fp HE H. unfold jet_elements_tappath_local.elements_tappath_env_rep in *. rep_stable_with HE H. Qed.

Lemma indexed_scalar_rep_stable {X} (elems_of : Elements.env -> list X) valz sz voff adelta cdelta :
  env_rep_sep_stable (indexed_scalar_rep elems_of valz sz voff adelta cdelta).
Proof. intros m m' env e fp HE H. unfold indexed_scalar_rep in *. rep_stable_with HE H. Qed.

Lemma indexed_ptr_rep_stable {E : Set} {X} (elems_of : E -> list X) elemrep sz poff adelta cdelta :
  elem_stable elemrep ->
  env_rep_sep_stable (indexed_ptr_rep elems_of elemrep sz poff adelta cdelta).
Proof. intros HS m m' env e fp HE H. unfold indexed_ptr_rep in *. rep_stable_with HE H. Qed.

Lemma annex_rep_stable :
  env_rep_sep_stable jet_elements_annex_local.elements_input_annex_hash_env_rep.
Proof. intros m m' env e fp HE H. unfold jet_elements_annex_local.elements_input_annex_hash_env_rep in *. rep_stable_with HE H. Qed.

Lemma pegin_rep_stable :
  env_rep_sep_stable jet_elements_pegin_local.elements_input_pegin_hash_env_rep.
Proof. intros m m' env e fp HE H. unfold jet_elements_pegin_local.elements_input_pegin_hash_env_rep in *. rep_stable_with HE H. Qed.

Create HintDb elements_stable.
#[export] Hint Resolve version_rep_stable locktime_rep_stable current_index_rep_stable
  script_cmr_rep_stable genesis_rep_stable hash_getter_rep_stable tapleaf_version_rep_stable
  tappath_rep_stable indexed_scalar_rep_stable indexed_ptr_rep_stable annex_rep_stable
  pegin_rep_stable hash_elem_rep_stable outpoint_rep_stable uint32_elem_stable : elements_stable.

Local Ltac bound := vm_compute; discriminate.
Local Ltac stable := eauto 8 with elements_stable.
Local Ltac runs_type T :=
  lazymatch T with
  | application_jet_local_spec ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_runs_on_fresh_frames f ge E A B r s)
  | application_jet_local_spec_sep ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_sep_runs_on_fresh_frames f ge E A B r s)
  end.
Local Ltac run H :=
  first [eapply application_jet_local_spec_executable
        |eapply application_jet_local_spec_sep_executable];
  [bound|bound|exact H|stable].

Theorem elements_input_annex_hash_local_spec_executable :
  ltac:(let T := type of C.jet_elements_annex_local.elements_input_annex_hash_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_annex_local.elements_input_annex_hash_local_spec. Qed.

Theorem elements_current_index_local_spec_executable :
  ltac:(let T := type of C.jet_elements_current_index_local.elements_current_index_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_current_index_local.elements_current_index_local_spec. Qed.

Theorem elements_genesis_block_hash_local_spec_executable :
  ltac:(let T := type of C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec. Qed.

Theorem elements_transaction_id_local_spec_executable :
  ltac:(let T := type of C.jet_elements_hash_field_jets.elements_transaction_id_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_hash_field_jets.elements_transaction_id_local_spec. Qed.

Theorem elements_internal_key_local_spec_executable :
  ltac:(let T := type of C.jet_elements_hash_field_jets.elements_internal_key_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_hash_field_jets.elements_internal_key_local_spec. Qed.

Theorem elements_output_script_hash_local_spec_executable :
  ltac:(let T := type of C.jet_elements_indexed_ptr_jets.elements_output_script_hash_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_indexed_ptr_jets.elements_output_script_hash_local_spec. Qed.

Theorem elements_input_prev_outpoint_local_spec_executable :
  ltac:(let T := type of C.jet_elements_indexed_ptr_jets.elements_input_prev_outpoint_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_indexed_ptr_jets.elements_input_prev_outpoint_local_spec. Qed.

Theorem elements_input_sequence_local_spec_executable :
  ltac:(let T := type of C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec. Qed.

Theorem elements_input_script_sig_hash_local_spec_executable :
  ltac:(let T := type of C.jet_elements_input_hash_jets.elements_input_script_sig_hash_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_input_hash_jets.elements_input_script_sig_hash_local_spec. Qed.

Theorem elements_input_script_hash_local_spec_executable :
  ltac:(let T := type of C.jet_elements_input_hash_jets.elements_input_script_hash_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_input_hash_jets.elements_input_script_hash_local_spec. Qed.

Theorem elements_issuance_asset_proof_local_spec_executable :
  ltac:(let T := type of C.jet_elements_input_hash_jets.elements_issuance_asset_proof_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_input_hash_jets.elements_issuance_asset_proof_local_spec. Qed.

Theorem elements_issuance_token_proof_local_spec_executable :
  ltac:(let T := type of C.jet_elements_input_hash_jets.elements_issuance_token_proof_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_input_hash_jets.elements_issuance_token_proof_local_spec. Qed.

Theorem elements_locktime_local_spec_executable :
  ltac:(let T := type of C.jet_elements_locktime_local.elements_locktime_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_locktime_local.elements_locktime_local_spec. Qed.

Theorem elements_output_surjection_proof_local_spec_executable :
  ltac:(let T := type of C.jet_elements_output_proof_jets.elements_output_surjection_proof_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_output_proof_jets.elements_output_surjection_proof_local_spec. Qed.

Theorem elements_output_range_proof_local_spec_executable :
  ltac:(let T := type of C.jet_elements_output_proof_jets.elements_output_range_proof_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_output_proof_jets.elements_output_range_proof_local_spec. Qed.

Theorem elements_input_pegin_hash_local_spec_executable :
  ltac:(let T := type of C.jet_elements_pegin_local.elements_input_pegin_hash_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_pegin_local.elements_input_pegin_hash_local_spec. Qed.

Theorem elements_script_cmr_local_spec_executable :
  ltac:(let T := type of C.jet_elements_script_cmr_local.elements_script_cmr_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_script_cmr_local.elements_script_cmr_local_spec. Qed.

Theorem elements_tapleaf_version_local_spec_executable :
  ltac:(let T := type of C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec. Qed.

Theorem elements_tappath_local_spec_executable :
  ltac:(let T := type of C.jet_elements_tappath_local.elements_tappath_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_tappath_local.elements_tappath_local_spec. Qed.

Theorem elements_version_local_spec_executable :
  ltac:(let T := type of C.jet_elements_version_local.elements_version_local_spec in let R := runs_type T in exact R).
Proof. run C.jet_elements_version_local.elements_version_local_spec. Qed.

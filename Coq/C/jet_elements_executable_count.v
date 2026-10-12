(** The Elements num_inputs and num_outputs jets run on fresh frames from any
    represented environment (continuation of [jet_elements_executable_lock]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_elements_prim C.jet_elements_executable.
Require Import C.jet_elements_count_local.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma elements_count_env_rep_stable delta count : env_rep_stable (elements_count_env_rep delta count).
Proof. intros m m' env e HE H. unfold elements_count_env_rep in *. rep_stable_with HE H. Qed.

Local Ltac bound := vm_compute; discriminate.

Theorem elements_num_inputs_local_spec_executable :
  ltac:(lazymatch type of elements_num_inputs_local_spec with
        | application_jet_local_spec ?f ?ge ?E ?A ?B ?r ?s =>
            exact (application_runs_on_fresh_frames f ge E A B r s) end).
Proof.
  eapply application_jet_local_spec_executable;
    [bound|bound|exact elements_num_inputs_local_spec|apply elements_count_env_rep_stable].
Qed.

Theorem elements_num_outputs_local_spec_executable :
  ltac:(lazymatch type of elements_num_outputs_local_spec with
        | application_jet_local_spec ?f ?ge ?E ?A ?B ?r ?s =>
            exact (application_runs_on_fresh_frames f ge E A B r s) end).
Proof.
  eapply application_jet_local_spec_executable;
    [bound|bound|exact elements_num_outputs_local_spec|apply elements_count_env_rep_stable].
Qed.

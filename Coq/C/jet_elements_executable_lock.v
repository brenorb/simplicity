(** The Elements lock-time jets run on fresh frames from any represented
    environment (continuation of [jet_elements_executable_current]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_elements_prim C.jet_elements_executable.
Require Import C.jet_elements_is_final_local C.jet_elements_lock_local C.jet_elements_check_lock.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma elements_tx_is_final_env_rep_stable : env_rep_sep_stable elements_tx_is_final_env_rep.
Proof. intros m m' env e fp HE H. unfold elements_tx_is_final_env_rep in *. rep_stable_with HE H. Qed.

Lemma elements_lock_env_rep_stable : env_rep_sep_stable elements_lock_env_rep.
Proof. intros m m' env e fp HE H. unfold elements_lock_env_rep in *. rep_stable_with HE H. Qed.

Lemma elements_check_lock_env_rep_stable : env_rep_stable elements_check_lock_env_rep.
Proof.
  intros m m' env e HE [fp H]. exists fp. exact (elements_lock_env_rep_stable _ _ _ _ _ HE H).
Qed.

Local Ltac bound := vm_compute; discriminate.
Local Ltac runs_type T :=
  lazymatch T with
  | application_jet_local_spec_sep ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_sep_runs_on_fresh_frames f ge E A B r s)
  | application_jet_partial_spec ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_partial_runs_on_fresh_frames f ge E A B r s)
  end.
Local Ltac run H S :=
  first [eapply application_jet_local_spec_sep_executable
        |eapply application_jet_partial_spec_executable];
  [bound|bound|exact H|exact S].

Theorem elements_tx_is_final_local_spec_executable :
  ltac:(let T := type of elements_tx_is_final_local_spec in let R := runs_type T in exact R).
Proof. run elements_tx_is_final_local_spec elements_tx_is_final_env_rep_stable. Qed.

Theorem elements_tx_lock_height_local_spec_executable :
  ltac:(let T := type of elements_tx_lock_height_local_spec in let R := runs_type T in exact R).
Proof. run elements_tx_lock_height_local_spec elements_lock_env_rep_stable. Qed.

Theorem elements_tx_lock_time_local_spec_executable :
  ltac:(let T := type of elements_tx_lock_time_local_spec in let R := runs_type T in exact R).
Proof. run elements_tx_lock_time_local_spec elements_lock_env_rep_stable. Qed.

Theorem elements_check_lock_height_local_spec_executable :
  ltac:(let T := type of elements_check_lock_height_local_spec in let R := runs_type T in exact R).
Proof. run elements_check_lock_height_local_spec elements_check_lock_env_rep_stable. Qed.

Theorem elements_check_lock_time_local_spec_executable :
  ltac:(let T := type of elements_check_lock_time_local_spec in let R := runs_type T in exact R).
Proof. run elements_check_lock_time_local_spec elements_check_lock_env_rep_stable. Qed.

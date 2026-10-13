(** Stability of the Bitcoin environment relations under memory extension.

    Every environment relation used by a registered Bitcoin jet observes the
    C environment only through loads that succeed in the given memory.  Such
    loads keep their value in any [memory_extension] (new blocks, unchanged
    loads on existing blocks), so each relation is stable.  These lemmas are
    the side condition of the executability theorems in
    [jet_frame_constructible_app]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_uint32_array_init C.jet_frame_constructible_app.
Require Import C.jet_bitcoin_version_local C.jet_bitcoin_locktime_local.
Require Import C.jet_bitcoin_current_index_local C.jet_bitcoin_count_local.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_input_value_local.
Require Import C.jet_bitcoin_indexed_scalar C.jet_bitcoin_current_jets.
Require Import C.jet_bitcoin_indexed_ptr C.jet_bitcoin_indexed_ptr_jets C.jet_bitcoin_current_ptr_jets.
Require Import C.jet_bitcoin_ext_ptr_jets C.jet_bitcoin_hash_getter_local C.jet_bitcoin_raw_jets.
Require Import C.jet_bitcoin_tapleaf_version_local C.jet_bitcoin_tappath_local.
Require Import C.jet_bitcoin_annex_local C.jet_bitcoin_current_annex_local.
Require Import C.jet_bitcoin_totals_local C.jet_bitcoin_fee_local C.jet_bitcoin_is_final_local.
Require Import C.jet_bitcoin_lock_local C.jet_bitcoin_distance_local C.jet_bitcoin_check_lock.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma uint32_array_at_extension m m' b base xs :
  memory_extension m m' -> uint32_array_at m b base xs -> uint32_array_at m' b base xs.
Proof.
  intros HE H i x Hx. eapply memory_extension_load; [exact HE|exact (H i x Hx)].
Qed.

(** Element relations of the indexed environment relations. *)
Definition elem_stable {X : Type} (elemrep : mem -> block -> Z -> X -> Prop) : Prop :=
  forall m m' b ofs x, memory_extension m m' -> elemrep m b ofs x -> elemrep m' b ofs x.

Lemma hash_elem_rep_stable : elem_stable hash_elem_rep.
Proof.
  intros m m' b ofs h HE H. unfold hash_elem_rep in *.
  eapply uint32_array_at_extension; eassumption.
Qed.

Lemma outpoint_rep_stable : elem_stable outpoint_rep.
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply uint32_array_at_extension; eassumption.
  - eapply memory_extension_load; eassumption.
Qed.

Lemma annex_elem_rep_stable : elem_stable annex_elem_rep.
Proof.
  intros m m' b ofs o HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros h Hh. eapply hash_elem_rep_stable; [exact HE|exact (H2 h Hh)].
Qed.

Lemma uint32_elem_stable {X : Type} (words : X -> list int) :
  elem_stable (fun m b ofs x => uint32_array_at m b ofs (words x)).
Proof.
  intros m m' b ofs x HE H. eapply uint32_array_at_extension; eassumption.
Qed.

(** Rebuild a relation in the extended memory with the same witnesses: keep
    the pure facts and transport each successful load. *)
Ltac ext_fact HE :=
  first
  [ eassumption
  | eapply (memory_extension_load _ _ _ _ _ _ HE); eassumption
  | eapply (uint32_array_at_extension _ _ _ _ _ HE); eassumption
  | (intros; eapply (memory_extension_load _ _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (uint32_array_at_extension _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (hash_elem_rep_stable _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (annex_elem_rep_stable _ _ _ _ _ HE); eauto; fail)
  | (intros; eapply (outpoint_rep_stable _ _ _ _ _ HE); eauto; fail)
  | (intros; match goal with HS : elem_stable _ |- _ => eapply (HS _ _ _ _ _ HE); eauto end; fail) ].

Ltac rep_stable_with HE H :=
  repeat match type of H with
  | exists _, _ => let x := fresh "x" in destruct H as [x H]; exists x
  end;
  repeat match goal with
  | H0 : _ /\ _ |- _ => destruct H0
  end;
  repeat split; ext_fact HE.

Lemma bitcoin_version_env_rep_stable : env_rep_stable bitcoin_version_env_rep.
Proof. intros m m' env e HE H. unfold bitcoin_version_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_locktime_env_rep_stable : env_rep_stable bitcoin_locktime_env_rep.
Proof. intros m m' env e HE H. unfold bitcoin_locktime_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_current_index_env_rep_stable : env_rep_stable bitcoin_current_index_env_rep.
Proof. intros m m' env e HE H. unfold bitcoin_current_index_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_count_env_rep_stable delta count :
  env_rep_stable (bitcoin_count_env_rep delta count).
Proof. intros m m' env e HE H. unfold bitcoin_count_env_rep in *. rep_stable_with HE H. Qed.

Lemma current_scalar_rep_stable {X} (elems_of : Bitcoin.env -> list X) valz sz voff adelta cdelta :
  env_rep_stable (current_scalar_rep elems_of valz sz voff adelta cdelta).
Proof. intros m m' env e HE H. unfold current_scalar_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_distance_env_rep_stable : env_rep_stable bitcoin_distance_env_rep.
Proof. intros m m' env e HE H. unfold bitcoin_distance_env_rep in *. rep_stable_with HE H. Qed.

(** Relations with a separation footprint. *)
Lemma bitcoin_script_cmr_env_rep_stable : env_rep_sep_stable bitcoin_script_cmr_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_script_cmr_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_input_value_env_rep_stable : env_rep_sep_stable bitcoin_input_value_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_input_value_env_rep in *. rep_stable_with HE H. Qed.

Lemma indexed_scalar_rep_stable {X} (elems_of : Bitcoin.env -> list X) valz sz voff adelta cdelta :
  env_rep_sep_stable (indexed_scalar_rep elems_of valz sz voff adelta cdelta).
Proof. intros m m' env e fp HE H. unfold indexed_scalar_rep in *. rep_stable_with HE H. Qed.

Lemma indexed_ptr_rep_stable {E : Set} {X} (elems_of : E -> list X) elemrep sz poff adelta cdelta :
  elem_stable elemrep ->
  env_rep_sep_stable (indexed_ptr_rep elems_of elemrep sz poff adelta cdelta).
Proof. intros HS m m' env e fp HE H. unfold indexed_ptr_rep in *. rep_stable_with HE H. Qed.

Lemma current_ptr_rep_stable {E : Set} {X} (elems_of : E -> list X) ix_of elemrep sz poff adelta cdelta :
  elem_stable elemrep ->
  env_rep_sep_stable (current_ptr_rep elems_of ix_of elemrep sz poff adelta cdelta).
Proof. intros HS m m' env e fp HE H. unfold current_ptr_rep in *. rep_stable_with HE H. Qed.

Lemma hash_getter_rep_stable {E : Set} (hash_of : E -> _) pdelta hdelta psz :
  env_rep_sep_stable (hash_getter_rep hash_of pdelta hdelta psz).
Proof. intros m m' env e fp HE H. unfold hash_getter_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_tapleaf_version_env_rep_stable : env_rep_sep_stable bitcoin_tapleaf_version_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_tapleaf_version_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_tappath_env_rep_stable : env_rep_sep_stable bitcoin_tappath_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_tappath_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_input_annex_hash_env_rep_stable : env_rep_sep_stable bitcoin_input_annex_hash_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_input_annex_hash_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_current_annex_hash_env_rep_stable :
  env_rep_sep_stable bitcoin_current_annex_hash_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_current_annex_hash_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_tx64_env_rep_stable delta total :
  env_rep_sep_stable (bitcoin_tx64_env_rep delta total).
Proof. intros m m' env e fp HE H. unfold bitcoin_tx64_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_fee_env_rep_stable : env_rep_sep_stable bitcoin_fee_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_fee_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_tx_is_final_env_rep_stable : env_rep_sep_stable bitcoin_tx_is_final_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_tx_is_final_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_lock_env_rep_stable : env_rep_sep_stable bitcoin_lock_env_rep.
Proof. intros m m' env e fp HE H. unfold bitcoin_lock_env_rep in *. rep_stable_with HE H. Qed.

Lemma bitcoin_check_lock_env_rep_stable : env_rep_stable bitcoin_check_lock_env_rep.
Proof.
  intros m m' env e HE [fp H]. exists fp. exact (bitcoin_lock_env_rep_stable _ _ _ _ _ HE H).
Qed.

Lemma raw_env_rep_stable rep :
  env_rep_sep_stable rep -> env_rep_sep_stable (raw_env_rep rep).
Proof.
  intros HS m m' env e fp HE [Hpath H]. exists Hpath. exact (HS _ _ _ _ _ HE H).
Qed.

(** Named instances. *)
Lemma bitcoin_num_inputs_env_rep_stable : env_rep_stable bitcoin_num_inputs_env_rep.
Proof. apply bitcoin_count_env_rep_stable. Qed.

Lemma bitcoin_num_outputs_env_rep_stable : env_rep_stable bitcoin_num_outputs_env_rep.
Proof. apply bitcoin_count_env_rep_stable. Qed.

Lemma bitcoin_total_input_value_env_rep_stable :
  env_rep_sep_stable bitcoin_total_input_value_env_rep.
Proof. apply bitcoin_tx64_env_rep_stable. Qed.

Lemma bitcoin_total_output_value_env_rep_stable :
  env_rep_sep_stable bitcoin_total_output_value_env_rep.
Proof. apply bitcoin_tx64_env_rep_stable. Qed.

Create HintDb env_stable.
#[export] Hint Resolve
  bitcoin_version_env_rep_stable bitcoin_locktime_env_rep_stable
  bitcoin_current_index_env_rep_stable bitcoin_num_inputs_env_rep_stable
  bitcoin_num_outputs_env_rep_stable current_scalar_rep_stable
  bitcoin_distance_env_rep_stable bitcoin_check_lock_env_rep_stable
  bitcoin_script_cmr_env_rep_stable bitcoin_input_value_env_rep_stable
  indexed_scalar_rep_stable indexed_ptr_rep_stable current_ptr_rep_stable
  hash_getter_rep_stable bitcoin_tapleaf_version_env_rep_stable
  bitcoin_tappath_env_rep_stable bitcoin_input_annex_hash_env_rep_stable
  bitcoin_current_annex_hash_env_rep_stable
  bitcoin_total_input_value_env_rep_stable bitcoin_total_output_value_env_rep_stable
  bitcoin_fee_env_rep_stable bitcoin_tx_is_final_env_rep_stable bitcoin_lock_env_rep_stable
  raw_env_rep_stable hash_elem_rep_stable outpoint_rep_stable annex_elem_rep_stable
  uint32_elem_stable : env_stable.

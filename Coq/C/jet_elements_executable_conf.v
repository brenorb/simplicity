(** The Elements confidential-value and issuance jets run on fresh frames from
    any represented environment (continuation of [jet_elements_executable]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_uint32_array_init.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_elements_prim.
Require Import C.jet_elements_indexed_ptr C.jet_elements_executable.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma asset_rep_stable a : forall m m' b ofs, memory_extension m m' ->
  asset_rep m b ofs a -> asset_rep m' b ofs a.
Proof.
  intros m m' b ofs HE [H1 H2]. split.
  - eapply uint32_array_at_ext; eassumption.
  - eapply memory_extension_load; eassumption.
Qed.

Lemma amount_rep_stable a : forall m m' b ofs, memory_extension m m' ->
  amount_rep m b ofs a -> amount_rep m' b ofs a.
Proof.
  intros m m' b ofs HE [H1 H2]. split.
  - destruct a as [v|[odd x] p].
    + eapply memory_extension_load; eassumption.
    + eapply uint32_array_at_ext; eassumption.
  - eapply memory_extension_load; eassumption.
Qed.

Lemma input_asset_elem_stable :
  elem_stable (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))).
Proof. intros m m' b ofs x HE H. eapply asset_rep_stable; eassumption. Qed.

Lemma output_asset_elem_stable :
  elem_stable (fun m b ofs txo => asset_rep m b ofs (clearPrf (txoAsset txo))).
Proof. intros m m' b ofs x HE H. eapply asset_rep_stable; eassumption. Qed.

Lemma output_nonce_elem_stable :
  elem_stable (fun m b ofs txo => nonce_rep m b ofs (txoNonce txo)).
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - intros Hn. eapply uint32_array_at_ext; [exact HE|exact (H1 Hn)].
  - eapply memory_extension_load; eassumption.
Qed.

Lemma asset_amount_elem_stable {X} (ga : X -> assetWith unit) (gm : X -> amountWith unit) pa pm :
  elem_stable (fun m b ofs x => asset_rep m b (ofs + pa) (ga x) /\ amount_rep m b (ofs + pm) (gm x)).
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply asset_rep_stable; eassumption.
  - eapply amount_rep_stable; eassumption.
Qed.

Lemma issuance_hash_elem_stable delta gh : elem_stable (issuance_hash_rep delta gh).
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros h Hh. eapply uint32_array_at_ext; [exact HE|exact (H2 h Hh)].
Qed.

Lemma issuance_amount_elem_stable : elem_stable issuance_amount_rep.
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros i Hi. eapply amount_rep_stable; [exact HE|exact (H2 i Hi)].
Qed.

Local Ltac bound := vm_compute; discriminate.
Local Ltac runs_type T :=
  lazymatch T with
  | application_jet_local_spec_sep ?f ?ge ?E ?A ?B ?r ?s =>
      constr:(application_sep_runs_on_fresh_frames f ge E A B r s)
  end.
Local Ltac run H S :=
  eapply application_jet_local_spec_sep_executable;
  [bound|bound|exact H|apply indexed_ptr_rep_stable; exact S].

Theorem elements_input_asset_local_spec_executable :
  ltac:(let T := type of elements_input_asset_local_spec in let R := runs_type T in exact R).
Proof. run elements_input_asset_local_spec input_asset_elem_stable. Qed.

Theorem elements_output_asset_local_spec_executable :
  ltac:(let T := type of elements_output_asset_local_spec in let R := runs_type T in exact R).
Proof. run elements_output_asset_local_spec output_asset_elem_stable. Qed.

Theorem elements_output_nonce_local_spec_executable :
  ltac:(let T := type of elements_output_nonce_local_spec in let R := runs_type T in exact R).
Proof. run elements_output_nonce_local_spec output_nonce_elem_stable. Qed.

Theorem elements_input_amount_local_spec_executable :
  ltac:(let T := type of elements_input_amount_local_spec in let R := runs_type T in exact R).
Proof.
  run elements_input_amount_local_spec
    (asset_amount_elem_stable (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) 168 208).
Qed.

Theorem elements_output_amount_local_spec_executable :
  ltac:(let T := type of elements_output_amount_local_spec in let R := runs_type T in exact R).
Proof.
  run elements_output_amount_local_spec
    (asset_amount_elem_stable (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) 0 104).
Qed.

Theorem elements_reissuance_blinding_local_spec_executable :
  ltac:(let T := type of elements_reissuance_blinding_local_spec in let R := runs_type T in exact R).
Proof. run elements_reissuance_blinding_local_spec (issuance_hash_elem_stable 0 gh_blinding). Qed.

Theorem elements_new_issuance_contract_local_spec_executable :
  ltac:(let T := type of elements_new_issuance_contract_local_spec in let R := runs_type T in exact R).
Proof. run elements_new_issuance_contract_local_spec (issuance_hash_elem_stable 0 gh_contract). Qed.

Theorem elements_reissuance_entropy_local_spec_executable :
  ltac:(let T := type of elements_reissuance_entropy_local_spec in let R := runs_type T in exact R).
Proof. run elements_reissuance_entropy_local_spec (issuance_hash_elem_stable 72 gh_entropy). Qed.

Theorem elements_issuance_asset_amount_local_spec_executable :
  ltac:(let T := type of elements_issuance_asset_amount_local_spec in let R := runs_type T in exact R).
Proof. run elements_issuance_asset_amount_local_spec issuance_amount_elem_stable. Qed.

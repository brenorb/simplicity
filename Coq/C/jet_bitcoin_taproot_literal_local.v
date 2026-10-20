(** Complete original C jets, canonical Core trees, and startup preservation.
    The external memcpy and initialized SHA/tag requirements stay explicit. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jets_sha C.jet_memcpy_model C.jet_sha_tapdata_jet C.jet_sha_startup_state.
Require Import C.jet_bitcoin_build_tapleaf_jet C.jet_bitcoin_build_tapbranch_jet.
Require Import C.jet_bitcoin_taproot_literal.
Require C.jet_sha_startup_init.
Set Default Timeout 10.

Theorem bitcoin_build_tapleaf_literal_local_spec : memcpy_model ->
  sha_jet_local_spec_pre sha_tapleaf_pre f_simplicity_bitcoin_build_tapleaf_simplicity
    (Word 8) (Word 8) (@literal_build_tapleaf Alg.CoreFunSem).
Proof. rewrite literal_build_tapleaf_matches. exact bitcoin_build_tapleaf_simplicity_local_spec. Qed.

Theorem bitcoin_build_tapbranch_literal_local_spec : memcpy_model ->
  sha_jet_local_spec_pre sha_tapbranch_pre f_simplicity_bitcoin_build_tapbranch
    (Word 9) (Word 8) (@literal_build_tapbranch Alg.CoreFunSem).
Proof. rewrite literal_build_tapbranch_matches. exact bitcoin_build_tapbranch_local_spec. Qed.

Theorem bitcoin_build_tapleaf_literal_startup_spec : memcpy_model ->
  sha_startup_total_spec f_simplicity_bitcoin_build_tapleaf_simplicity
    (Word 8) (Word 8) (@literal_build_tapleaf Alg.CoreFunSem).
Proof.
  intro HModel. eapply sha_startup_total_from_pre.
  - vm_compute; reflexivity.
  - exact sha_startup_state_tapleaf.
  - exact (bitcoin_build_tapleaf_literal_local_spec HModel).
Qed.

Theorem bitcoin_build_tapbranch_literal_startup_spec : memcpy_model ->
  sha_startup_total_spec f_simplicity_bitcoin_build_tapbranch
    (Word 9) (Word 8) (@literal_build_tapbranch Alg.CoreFunSem).
Proof.
  intro HModel. eapply sha_startup_total_from_pre.
  - vm_compute; reflexivity.
  - exact sha_startup_state_tapbranch.
  - exact (bitcoin_build_tapbranch_literal_local_spec HModel).
Qed.

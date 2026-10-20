(** Whole original C calls, including assertion failure and memory framing. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jets_sha C.jet_memcpy_model C.jet_sha_ctx8_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_add_jets C.jet_sha_startup_state.
Require Import C.jet_bitcoin_outpoint_hash_jet C.jet_bitcoin_annex_hash_jet.
Require Import C.jet_bitcoin_ctx_hash_literal.
Require C.jet_sha_startup_init.
Set Default Timeout 10.

Theorem bitcoin_outpoint_hash_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_bitcoin_outpoint_hash
    (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type
    (@literal_bitcoin_outpoint_hash optalg).
Proof. rewrite literal_bitcoin_outpoint_hash_matches. exact bitcoin_outpoint_hash_local_spec. Qed.

Theorem bitcoin_annex_hash_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_bitcoin_annex_hash
    (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type
    (@literal_bitcoin_annex_hash optalg).
Proof. rewrite literal_bitcoin_annex_hash_matches. exact bitcoin_annex_hash_local_spec. Qed.

Theorem bitcoin_outpoint_hash_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_bitcoin_outpoint_hash
    (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type
    (@literal_bitcoin_outpoint_hash optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (bitcoin_outpoint_hash_literal_local_spec HModel).
Qed.

Theorem bitcoin_annex_hash_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_bitcoin_annex_hash
    (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type
    (@literal_bitcoin_annex_hash optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (bitcoin_annex_hash_literal_local_spec HModel).
Qed.

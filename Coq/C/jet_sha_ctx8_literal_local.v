(** Compose the literal canonical context-add bridge with the complete
    execution theorem for the original SHA translation unit. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jets_sha C.jet_memcpy_model C.jet_sha_ctx8_spec.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_ctx8_literal C.jet_sha_startup_state.
Require C.jet_sha_startup_init.
Set Default Timeout 10.

Theorem sha_256_ctx_8_add_1_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_1
    (Ty.Prod sha256_ctx8_type (Word 3)) sha256_ctx8_type
    (@literal_ctx8_add1 optalg).
Proof.
  rewrite literal_ctx8_add1_matches.
  exact sha_256_ctx_8_add_1_local_spec.
Qed.

Theorem sha_256_ctx_8_add_1_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_1
    (Ty.Prod sha256_ctx8_type (Word 3)) sha256_ctx8_type
    (@literal_ctx8_add1 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_1_literal_local_spec HModel).
Qed.

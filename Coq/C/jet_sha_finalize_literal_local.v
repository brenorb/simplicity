(** The complete original C finalizer against the literal canonical tree. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jets_sha C.jet_memcpy_model C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_add_jets C.jet_sha_ctx8_finalize_jet.
Require Import C.jet_sha_finalize_literal C.jet_sha_startup_state.
Require C.jet_sha_startup_init.
Set Default Timeout 10.

Theorem sha_256_ctx_8_finalize_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_finalize sha256_ctx8_type (Word 8)
    (@literal_ctx8_finalize optalg).
Proof.
  rewrite literal_ctx8_finalize_matches. exact sha_256_ctx_8_finalize_local_spec.
Qed.

Theorem sha_256_ctx_8_finalize_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_finalize sha256_ctx8_type (Word 8)
    (@literal_ctx8_finalize optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_finalize_literal_local_spec HModel).
Qed.

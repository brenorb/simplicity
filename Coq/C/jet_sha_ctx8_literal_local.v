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

Theorem sha_256_ctx_8_add_2_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_2
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 1)) sha256_ctx8_type
    (@literal_ctx8_addn 1 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_2_local_spec.
Qed.

Theorem sha_256_ctx_8_add_2_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_2
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 1)) sha256_ctx8_type
    (@literal_ctx8_addn 1 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_2_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_4_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_4
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 2)) sha256_ctx8_type
    (@literal_ctx8_addn 2 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_4_local_spec.
Qed.

Theorem sha_256_ctx_8_add_4_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_4
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 2)) sha256_ctx8_type
    (@literal_ctx8_addn 2 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_4_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_8_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_8
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 3)) sha256_ctx8_type
    (@literal_ctx8_addn 3 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_8_local_spec.
Qed.

Theorem sha_256_ctx_8_add_8_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_8
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 3)) sha256_ctx8_type
    (@literal_ctx8_addn 3 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_8_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_16_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_16
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 4)) sha256_ctx8_type
    (@literal_ctx8_addn 4 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_16_local_spec.
Qed.

Theorem sha_256_ctx_8_add_16_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_16
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 4)) sha256_ctx8_type
    (@literal_ctx8_addn 4 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_16_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_32_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_32
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 5)) sha256_ctx8_type
    (@literal_ctx8_addn 5 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_32_local_spec.
Qed.

Theorem sha_256_ctx_8_add_32_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_32
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 5)) sha256_ctx8_type
    (@literal_ctx8_addn 5 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_32_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_64_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_64
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 6)) sha256_ctx8_type
    (@literal_ctx8_addn 6 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_64_local_spec.
Qed.

Theorem sha_256_ctx_8_add_64_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_64
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 6)) sha256_ctx8_type
    (@literal_ctx8_addn 6 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_64_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_128_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_128
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 7)) sha256_ctx8_type
    (@literal_ctx8_addn 7 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_128_local_spec.
Qed.

Theorem sha_256_ctx_8_add_128_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_128
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 7)) sha256_ctx8_type
    (@literal_ctx8_addn 7 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_128_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_256_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_256
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 8)) sha256_ctx8_type
    (@literal_ctx8_addn 8 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_256_local_spec.
Qed.

Theorem sha_256_ctx_8_add_256_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_256
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 8)) sha256_ctx8_type
    (@literal_ctx8_addn 8 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_256_literal_local_spec HModel).
Qed.

Theorem sha_256_ctx_8_add_512_literal_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_512
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 9)) sha256_ctx8_type
    (@literal_ctx8_addn 9 optalg).
Proof.
  rewrite literal_ctx8_addn_matches.
  exact sha_256_ctx_8_add_512_local_spec.
Qed.

Theorem sha_256_ctx_8_add_512_literal_startup_spec : memcpy_model ->
  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_512
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 9)) sha256_ctx8_type
    (@literal_ctx8_addn 9 optalg).
Proof.
  intro HModel. apply sha_startup_partial_from_local.
  - vm_compute; reflexivity.
  - exact (sha_256_ctx_8_add_512_literal_local_spec HModel).
Qed.

(** Original public C initializer against the canonical TapData program. *)
Require Import Simplicity.Ty Simplicity.Alg.
Require Import C.jets_sha C.jet_memcpy_model C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_tapdata_jet C.jet_sha_tapdata_prep C.jet_sha_compress_call.
Require Import C.jet_sha_add_n_exec.
Require Import C.jet_tapdata_literal C.jet_sha_startup_state.
Require C.jet_sha_startup_init.
Set Default Timeout 10.

Theorem tapdata_init_literal_local_spec : memcpy_model ->
  sha_jet_local_spec_pre (fun m => sha_globals_ok m /\ sha_tag_ok m)
    f_simplicity_tapdata_init Ty.Unit sha256_ctx8_type (@literal_tapdata_init Alg.CoreFunSem).
Proof. rewrite literal_tapdata_init_matches. exact tapdata_init_local_spec. Qed.

Theorem tapdata_init_literal_startup_spec : memcpy_model ->
  sha_startup_total_spec f_simplicity_tapdata_init Ty.Unit sha256_ctx8_type
    (@literal_tapdata_init Alg.CoreFunSem).
Proof.
  intro HModel. eapply sha_startup_total_from_pre.
  - vm_compute; reflexivity.
  - exact sha_startup_state_tapdata.
  - exact (tapdata_init_literal_local_spec HModel).
Qed.

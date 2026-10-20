(** Reuse the actual SHA-unit C proof with the candidate literal term.
    Global-state requirements remain explicit; no registration is implied
    until canonical source correspondence and startup scope are reviewed. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jets_sha C.jet_sha_block_local C.jet_sha_block_literal C.jet_sha_startup_state.
Require Import C.jet_sha_startup_lifecycle C.jet_sha_tapdata_jet.
(** Also kernel-check existence of the actual initial memory/lifecycle. *)
Require C.jet_sha_startup_init.
Set Default Timeout 10.

Theorem sha_256_block_literal_local_spec :
  sha_jet_local_spec f_simplicity_sha_256_block (Ty.Prod Word256 Word512) Word256
    (@literal_sha_256_block Alg.CoreFunSem).
Proof.
  rewrite literal_sha_256_block_matches; exact sha_256_block_local_spec.
Qed.

Theorem sha_256_block_literal_lifecycle_spec :
  sha_jet_local_spec_pre (fun m => exists owned, sha_lifecycle m owned)
    f_simplicity_sha_256_block (Ty.Prod Word256 Word512) Word256
    (@literal_sha_256_block Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    [owned HLife] HBase HAlign HFields HCursor HMax HInput HOutput.
  exact (sha_256_block_literal_local_spec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    (sha_startup_state_dispatch m (proj1 (sha_lifecycle_state m owned HLife)))
    HBase HAlign HFields HCursor HMax HInput HOutput).
Qed.

Theorem sha_256_block_literal_startup_spec :
  sha_startup_total_spec f_simplicity_sha_256_block (Ty.Prod Word256 Word512) Word256
    (@literal_sha_256_block Alg.CoreFunSem).
Proof.
  apply sha_startup_total_from_local.
  - vm_compute; reflexivity.
  - exact sha_256_block_literal_local_spec.
Qed.

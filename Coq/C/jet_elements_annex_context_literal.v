(** Whole original Elements annex_hash, using the existing generic Elements
    partial-frame contract and the shared literal annex program. *)
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jets_elements C.jet_memcpy_model C.jet_sha_ctx8_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_nonce_local_actual C.jet_elements_sha_program C.jet_elements_annex_context_exec.
Require Import C.jet_bitcoin_ctx_hash_literal.
Set Default Timeout 10.

Theorem elements_annex_hash_literal_local_spec : memcpy_model ->
  nonce_elements_partial_local_spec f_simplicity_annex_hash
    (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type
    (@literal_bitcoin_annex_hash optalg).
Proof.
  rewrite literal_bitcoin_annex_hash_matches.
  intros HM env m bd dbase bs sbase bi bw edge outedge cursor rc a HG HB HA HF H0 HMax HI HO.
  apply nonce_globals_equiv in HG.
  pose proof (elements_annex_hash_local_spec HM env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HG HB HA HF H0 HMax HI HO) as HC.
  rewrite elements_sha_genv in HC. exact HC.
Qed.

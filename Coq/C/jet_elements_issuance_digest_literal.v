(** Six actual C optional issuance-digest getters, with one shared adapter
    to the checked literal index/digest conversion. Neither direct hash is
    hashed again; the issuance tag decides whether a field is present. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_ptr_jets.
Require Import C.jet_elements_issuance_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_current_sequence_literal C.jet_elements_optional_digest_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma elements_issuance_optional_digest_literal_matches gh a environment :
  Some (issuance_hash_result gh (sigTxIn (Elements.envTx environment)) a) =
    elements_input_optional_digest_literal_spec (fun txi => gh (sigTxiIssuance txi)) a environment.
Proof.
  unfold issuance_hash_result. apply elements_input_optional_digest_literal_matches.
Qed.

Definition elements_reissuance_blinding_literal_spec :=
  elements_input_optional_digest_literal_spec (fun txi => gh_blinding (sigTxiIssuance txi)).

Lemma elements_reissuance_blinding_literal_matches a environment :
  @elements_reissuance_blinding_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_reissuance_blinding_literal_spec a environment.
Proof.
  rewrite elements_reissuance_blinding_sem. unfold elements_reissuance_blinding_literal_spec.
  apply elements_issuance_optional_digest_literal_matches.
Qed.

Definition elements_current_reissuance_blinding_literal_spec :=
  elements_current_literal_result elements_reissuance_blinding_literal_spec.

Lemma elements_current_reissuance_blinding_literal_matches a environment :
  @elements_current_reissuance_blinding_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_reissuance_blinding_literal_spec a environment.
Proof.
  unfold elements_current_reissuance_blinding_spec, elements_current_reissuance_blinding_literal_spec.
  apply elements_current_literal_sem. exact elements_reissuance_blinding_literal_matches.
Qed.

Theorem elements_reissuance_blinding_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_reissuance_blinding elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep 0 gh_blinding) 544 256 0 696)
    elements_reissuance_blinding_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_reissuance_blinding_literal_matches|exact elements_reissuance_blinding_local_spec].
Qed.

Theorem elements_current_reissuance_blinding_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_reissuance_blinding elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx (issuance_hash_rep 0 gh_blinding) 544 256 0 696)
    elements_current_reissuance_blinding_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_reissuance_blinding_literal_matches|exact elements_current_reissuance_blinding_local_spec].
Qed.

Definition elements_new_issuance_contract_literal_spec :=
  elements_input_optional_digest_literal_spec (fun txi => gh_contract (sigTxiIssuance txi)).

Lemma elements_new_issuance_contract_literal_matches a environment :
  @elements_new_issuance_contract_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_new_issuance_contract_literal_spec a environment.
Proof.
  rewrite elements_new_issuance_contract_sem. unfold elements_new_issuance_contract_literal_spec.
  apply elements_issuance_optional_digest_literal_matches.
Qed.

Definition elements_current_new_issuance_contract_literal_spec :=
  elements_current_literal_result elements_new_issuance_contract_literal_spec.

Lemma elements_current_new_issuance_contract_literal_matches a environment :
  @elements_current_new_issuance_contract_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_new_issuance_contract_literal_spec a environment.
Proof.
  unfold elements_current_new_issuance_contract_spec, elements_current_new_issuance_contract_literal_spec.
  apply elements_current_literal_sem. exact elements_new_issuance_contract_literal_matches.
Qed.

Theorem elements_new_issuance_contract_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_new_issuance_contract elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep 0 gh_contract) 544 256 0 696)
    elements_new_issuance_contract_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_new_issuance_contract_literal_matches|exact elements_new_issuance_contract_local_spec].
Qed.

Theorem elements_current_new_issuance_contract_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_new_issuance_contract elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx (issuance_hash_rep 0 gh_contract) 544 256 0 696)
    elements_current_new_issuance_contract_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_new_issuance_contract_literal_matches|exact elements_current_new_issuance_contract_local_spec].
Qed.

Definition elements_reissuance_entropy_literal_spec :=
  elements_input_optional_digest_literal_spec (fun txi => gh_entropy (sigTxiIssuance txi)).

Lemma elements_reissuance_entropy_literal_matches a environment :
  @elements_reissuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_reissuance_entropy_literal_spec a environment.
Proof.
  rewrite elements_reissuance_entropy_sem. unfold elements_reissuance_entropy_literal_spec.
  apply elements_issuance_optional_digest_literal_matches.
Qed.

Definition elements_current_reissuance_entropy_literal_spec :=
  elements_current_literal_result elements_reissuance_entropy_literal_spec.

Lemma elements_current_reissuance_entropy_literal_matches a environment :
  @elements_current_reissuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_reissuance_entropy_literal_spec a environment.
Proof.
  unfold elements_current_reissuance_entropy_spec, elements_current_reissuance_entropy_literal_spec.
  apply elements_current_literal_sem. exact elements_reissuance_entropy_literal_matches.
Qed.

Theorem elements_reissuance_entropy_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_reissuance_entropy elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep 72 gh_entropy) 544 256 0 696)
    elements_reissuance_entropy_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_reissuance_entropy_literal_matches|exact elements_reissuance_entropy_local_spec].
Qed.

Theorem elements_current_reissuance_entropy_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_reissuance_entropy elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx (issuance_hash_rep 72 gh_entropy) 544 256 0 696)
    elements_current_reissuance_entropy_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_reissuance_entropy_literal_matches|exact elements_current_reissuance_entropy_local_spec].
Qed.


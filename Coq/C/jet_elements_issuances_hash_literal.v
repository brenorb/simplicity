(** Canonical composition of all four issuance hashes and the original C
    issuances_hash cache getter. Reuse the fixed-vector hash bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_elements_words_hash_program C.jet_sha_hash_words_reader.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_elements_issuance_entropy_spec.
Require Import C.jet_elements_composite_amounts_hash C.jet_elements_composite_hash_literal.
Require Import C.jet_bitcoin_composite_hash.
Require Import C.jet_elements_issuance_amounts_hash_program C.jet_elements_issuance_amounts_hash_literal.
Require Import C.jet_elements_issuance_proofs_hash_program C.jet_elements_issuance_proofs_hash_literal.
Require Import C.jet_elements_blinding_entropy_hash_program C.jet_elements_blinding_entropy_literal.
Require Import C.jet_elements_blinding_entropy_canonical.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_issuances_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @elements_fixed_vector_hash_spec 7 alg
    (@AC.pair _ _ _ core
      (@AC.pair _ _ _ core (@elements_issuance_asset_amounts_hash_spec alg)
        (@elements_issuance_token_amounts_hash_spec alg))
      (@AC.pair _ _ _ core (@elements_issuance_range_proofs_hash_spec alg)
        (@literal_issuance_blinding_entropy_hash_spec alg))).

Lemma elements_issuances_hash_spec_parametric : EFP.Parametric (@elements_issuances_hash_spec).
Proof.
  unfold elements_issuances_hash_spec. cbv zeta.
  apply elements_fixed_vector_hash_spec_parametric. intros alg1 alg2 R.
  pose proof (elements_issuance_amounts_hash_spec_parametric (@elements_issuance_asset_spec)
    Elements.IssuanceAssetAmount elements_issuance_asset_spec_parametric alg1 alg2 R) as HA.
  pose proof (elements_issuance_amounts_hash_spec_parametric (@elements_issuance_token_spec)
    Elements.IssuanceTokenAmount elements_issuance_token_spec_parametric alg1 alg2 R) as HT.
  pose proof (elements_issuance_range_proofs_hash_spec_parametric alg1 alg2 R) as HR.
  pose proof (literal_issuance_blinding_entropy_hash_spec_parametric alg1 alg2 R) as HB.
  destruct R as [R [[HC HAm] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.pair_Parametric RC); apply (Alg.pair_Parametric RC); assumption.
Qed.

Definition elements_issuances_hash_of (e : Elements.env) : hash256 :=
  sha256_bytes_of (vector_values Word8 7
    ((from_hash256 (elements_issuance_asset_amounts_hash_of e),
      from_hash256 (elements_issuance_token_amounts_hash_of e)),
     (from_hash256 (elements_issuance_range_proofs_hash_of e),
      from_hash256 (elements_issuance_blinding_entropy_hash_of e)))).

Theorem elements_issuances_hash_spec_sem e :
  @elements_issuances_hash_spec elements_hash_alg tt e = Some (from_hash256 (elements_issuances_hash_of e)).
Proof.
  unfold elements_issuances_hash_spec, elements_issuances_hash_of. cbv zeta.
  apply elements_fixed_vector_hash_spec_sem.
  - rewrite !(hr_pair Elements.env).
    rewrite (elements_issuance_amounts_hash_spec_sem (@elements_issuance_asset_spec)
      Elements.IssuanceAssetAmount elements_issuance_asset_pairs elements_issuance_asset_pairs_sem).
    rewrite (elements_issuance_amounts_hash_spec_sem (@elements_issuance_token_spec)
      Elements.IssuanceTokenAmount elements_issuance_token_pairs elements_issuance_token_pairs_sem).
    rewrite elements_issuance_range_proofs_hash_spec_sem, literal_issuance_blinding_entropy_hash_spec_sem.
    reflexivity.
  - vm_compute; reflexivity.
Qed.

Theorem elements_issuances_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_issuances_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuances_hash_of 0 600 760)
    (fun a e => @elements_issuances_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _issuancesHash).
  - exact elements_issuances_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

Definition literal_elements_issuances_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @literal_elements_fixed_vector_hash 7 alg
    (@AC.pair _ _ _ core
      (@AC.pair _ _ _ core (@literal_elements_issuance_asset_amounts_hash alg)
        (@literal_elements_issuance_token_amounts_hash alg))
      (@AC.pair _ _ _ core (@literal_elements_issuance_range_proofs_hash alg)
        (@literal_elements_issuance_blinding_entropy_hash alg))).

Lemma literal_elements_issuances_hash_matches alg :
  @literal_elements_issuances_hash alg = @elements_issuances_hash_spec alg.
Proof.
  unfold literal_elements_issuances_hash, elements_issuances_hash_spec.
  rewrite (literal_elements_issuance_asset_amounts_hash_matches alg).
  rewrite (literal_elements_issuance_token_amounts_hash_matches alg).
  rewrite (literal_elements_issuance_range_proofs_hash_matches alg).
  rewrite (literal_elements_issuance_blinding_entropy_hash_matches alg).
  apply literal_elements_fixed_vector_hash_matches.
Qed.

Lemma literal_elements_issuances_hash_parametric : EFP.Parametric (@literal_elements_issuances_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuances_hash_matches alg1), (literal_elements_issuances_hash_matches alg2).
  exact (elements_issuances_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuances_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuances_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuances_hash_of 0 600 760)
    (fun a environment => @literal_elements_issuances_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_issuances_hash_matches.
  exact elements_issuances_hash_program_local_spec.
Qed.

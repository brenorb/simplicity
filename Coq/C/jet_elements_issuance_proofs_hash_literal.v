(** Canonical two-primitive issuance proof loop and original C cache getter.
    Both primitive lookups and both early exits are retained. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_elements_issuance_proofs_hash_program.
Require Import C.jet_elements_issuance_proof_literal.
Require Import C.jet_sha256_ctx8_init_spec C.jet_forWhile_spec.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_elements_issuance_asset_proof_view_matches txi :
  elements_issuance_asset_proof_bytes txi = haskell_issuance_proof_view false txi.
Proof.
  change (jet_elements_input_hash_jets.issuance_asset_proof_bytes txi = haskell_issuance_proof_view false txi).
  exact (elements_issuance_asset_proof_view_matches txi).
Qed.

Lemma literal_elements_issuance_token_proof_view_matches txi :
  elements_issuance_token_proof_bytes txi = haskell_issuance_proof_view true txi.
Proof.
  change (jet_elements_input_hash_jets.issuance_token_proof_bytes txi = haskell_issuance_proof_view true txi).
  exact (elements_issuance_token_proof_view_matches txi).
Qed.

Definition literal_elements_issuance_proofs_body {alg : EFP.Algebra} :
    EFP.domain alg (Ty.Prod (Ty.Prod Ty.Unit Word32) sha256_ctx8_type)
      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof)))
      (@AC.pair _ _ _ core
        (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof)))
        (AC.drop AC.iden)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden))
          (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.drop AC.iden))))
        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
          (@AC.injr _ _ _ core (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (AC.drop (AC.drop AC.iden))
              (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden)) (AC.take AC.iden)))
            (@literal_ctx8_addn 6 term)))))).


Lemma literal_elements_issuance_proofs_body_matches alg :
  @literal_elements_issuance_proofs_body alg = @elements_issuance_proofs_body alg.
Proof.
  unfold literal_elements_issuance_proofs_body, elements_issuance_proofs_body.
  rewrite literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Definition literal_elements_issuance_range_proofs_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
    (@AC.comp _ _ _ core
      (@for_while_program 5 _ _ _ core (@literal_elements_issuance_proofs_body alg))
      (@AC.copair _ _ _ core (@literal_ctx8_finalize term) (@literal_ctx8_finalize term))).


Lemma literal_elements_issuance_range_proofs_hash_matches alg :
  @literal_elements_issuance_range_proofs_hash alg = @elements_issuance_range_proofs_hash_spec alg.
Proof.
  unfold literal_elements_issuance_range_proofs_hash, elements_issuance_range_proofs_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_issuance_proofs_body_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_issuance_range_proofs_hash_parametric :
  EFP.Parametric (@literal_elements_issuance_range_proofs_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_range_proofs_hash_matches alg1),
    (literal_elements_issuance_range_proofs_hash_matches alg2).
  exact (elements_issuance_range_proofs_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuance_range_proofs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_range_proofs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_range_proofs_hash_of 0 536 760)
    (fun a environment => @literal_elements_issuance_range_proofs_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_issuance_range_proofs_hash_matches.
  exact elements_issuance_range_proofs_hash_program_local_spec.
Qed.

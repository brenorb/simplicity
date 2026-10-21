(** Literal canonical indexed issuanceHash program, with shared issuance
    calculations/serializers and the actual one8 blinding program. Support
    only: there is no whole-C endpoint in this module. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_elements_prim C.jet_elements_words_hash_program.
Require Import C.jet_elements_single_issuance_spec C.jet_elements_issuance_amount_hash_spec.
Require Import C.jet_elements_issuance_amounts_hash_program C.jet_elements_issuance_amounts_hash_literal.
Require Import C.jet_elements_issuance_entropy_spec.
Require Import C.jet_elements_blinding_entropy_spec C.jet_elements_blinding_entropy_canonical.
Require Import C.jet_elements_blinding_entropy_literal.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal.
Require Import C.jet_sha_hash_words_literal C.jet_sha_finalize_literal C.jet_bitcoin_vh_hash_spec.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Set Default Timeout 10.

Definition literal_elements_single_issuance_payload {term : Alg.Assertion.Algebra} :
    term (Ty.Prod issuance_asset_amount_value_type elements_single_issuance_tail_type) Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp
            (AC.pair
              (AC.comp
                (AC.pair
                  (AC.comp
                    (AC.pair (AC.comp AC.unit (@literal_sha_hash_ctx_init core)) (AC.take AC.iden))
                    (@literal_issuance_asset_amount_absorb term))
                  (AC.drop (AC.take (@assert_iden_spec issuance_asset_amount_value_type term))))
                (@literal_issuance_asset_amount_absorb term))
              (AC.drop (AC.drop (AC.take (AC.take (@assert_iden_spec Word256 term))))))
            (@literal_ctx8_addn 5 term))
          (AC.drop (AC.drop (AC.take (AC.drop (@assert_iden_spec Word256 term))))))
        (@literal_ctx8_addn 5 term))
      (AC.drop (AC.drop (AC.drop (@assert_iden_spec blinding_entropy_value_type term)))))
    (AC.comp (@literal_elements_blinding_entropy_absorb term) (@literal_ctx8_finalize term)).

Lemma literal_elements_single_issuance_payload_matches term :
  @literal_elements_single_issuance_payload term = @elements_single_issuance_payload_spec term.
Proof.
  unfold literal_elements_single_issuance_payload, elements_single_issuance_payload_spec.
  rewrite literal_sha_hash_ctx_init_matches, !literal_issuance_asset_amount_absorb_matches,
    !literal_ctx8_addn_algebra_matches, literal_elements_blinding_entropy_absorb_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_single_issuance_hash {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit Word256) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (@literal_elements_issuance_asset_pair alg)
      (AC.pair
        (@literal_elements_issuance_token_pair alg)
        (AC.pair
          (AC.pair (@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof)
            (@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof))
          (@elements_issuance_blinding_entropy_spec alg))))
    (AC.case (AC.injl AC.unit) (AC.injr (@literal_elements_single_issuance_payload term))).

Lemma literal_elements_single_issuance_hash_matches alg :
  @literal_elements_single_issuance_hash alg = @elements_single_issuance_hash_spec alg.
Proof.
  unfold literal_elements_single_issuance_hash, elements_single_issuance_hash_spec.
  rewrite literal_elements_issuance_asset_pair_matches, literal_elements_issuance_token_pair_matches,
    literal_elements_single_issuance_payload_matches. reflexivity.
Qed.

Lemma literal_elements_single_issuance_hash_parametric :
  EFP.Parametric (@literal_elements_single_issuance_hash).
Proof.
  intros alg1 alg2 R. rewrite (literal_elements_single_issuance_hash_matches alg1),
    (literal_elements_single_issuance_hash_matches alg2).
  exact (elements_single_issuance_hash_parametric alg1 alg2 R).
Qed.

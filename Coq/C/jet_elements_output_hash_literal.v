(** Whole original Elements output_hash against the literal primitive-bearing
    SigHash outputHash program. Initial field representation, SHA readiness
    and memcpy_model remain explicit caller/library obligations. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_elements_amount_jets C.jet_elements_words_hash_program.
Require Import C.jet_elements_amounts_hash_literal C.jet_elements_nonces_hash_literal.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_nonce_hash_spec.
Require Import C.jet_elements_output_hash_spec C.jet_elements_output_hash_jet.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal.
Require Import C.jet_sha_hash_words_literal C.jet_sha_finalize_literal C.jet_bitcoin_vh_hash_spec.
Require Import C.jet_memcpy_model C.jet_elements_sha_program.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Set Default Timeout 10.

Definition literal_elements_output_hash_payload {term : Alg.Assertion.Algebra} :
    term (Ty.Prod elements_asset_amount_type elements_output_hash_tail_type) Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp
            (AC.pair
              (AC.comp
                (AC.pair (AC.comp AC.unit (@literal_sha_hash_ctx_init core)) (AC.take AC.iden))
                (@literal_elements_asset_amount_hash term))
              (AC.drop (AC.take (@assert_iden_spec elements_nonce_type term))))
            (@literal_elements_nonce_hash term))
          (AC.drop (AC.drop (AC.take (@assert_iden_spec Word256 term)))))
        (@literal_ctx8_addn 5 term))
      (AC.drop (AC.drop (AC.drop (@assert_iden_spec Word256 term)))))
    (AC.comp (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_elements_output_hash_payload_matches term :
  @literal_elements_output_hash_payload term = @elements_output_hash_payload_spec term.
Proof.
  unfold literal_elements_output_hash_payload, elements_output_hash_payload_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_asset_amount_hash_matches,
    literal_elements_nonce_hash_matches, !literal_ctx8_addn_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_output_hash {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit Word256) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair (@elements_output_amount_spec alg)
      (AC.pair (@EFP.Combinators.prim _ _ alg Elements.OutputNonce)
        (AC.pair (@EFP.Combinators.prim _ _ alg Elements.OutputScriptHash)
          (@EFP.Combinators.prim _ _ alg Elements.OutputRangeProof))))
    (AC.case (AC.injl AC.unit) (AC.injr (@literal_elements_output_hash_payload term))).

Lemma literal_elements_output_hash_matches alg :
  @literal_elements_output_hash alg = @elements_output_hash_spec alg.
Proof.
  unfold literal_elements_output_hash, elements_output_hash_spec.
  rewrite literal_elements_output_hash_payload_matches. reflexivity.
Qed.

Lemma literal_elements_output_hash_parametric : EFP.Parametric (@literal_elements_output_hash).
Proof.
  intros alg1 alg2 R. rewrite (literal_elements_output_hash_matches alg1),
    (literal_elements_output_hash_matches alg2).
  exact (elements_output_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_output_hash_literal_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_output_hash elements_ge Elements.env
    Word32 (Ty.Sum Ty.Unit Word256) elements_output_hash_rep
    (fun a environment => @literal_elements_output_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_output_hash_matches.
  rewrite <- elements_sha_genv. exact elements_output_hash_program_local_spec.
Qed.

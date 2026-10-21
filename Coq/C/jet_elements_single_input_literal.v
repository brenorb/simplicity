(** Literal primitive-bearing Elements inputHash program; no C endpoint yet. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_elements_prim C.jet_elements_words_hash_program.
Require Import C.jet_elements_single_input_hash_spec C.jet_elements_outpoints_hash_program.
Require Import C.jet_elements_inputs_hash_literal C.jet_bitcoin_ctx_hash_literal C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_bitcoin_inputs_hash_literal.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal.
Require Import C.jet_sha_hash_words_literal C.jet_sha_finalize_literal C.jet_bitcoin_vh_hash_spec.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Set Default Timeout 10.

Definition literal_elements_single_input_payload {term : Alg.Assertion.Algebra} :
    term (Ty.Prod (Ty.Sum Ty.Unit Word256) elements_single_input_tail_type) Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp
            (AC.pair
              (AC.comp AC.unit (@literal_sha_hash_ctx_init core))
              (AC.pair (AC.take AC.iden)
                (AC.drop (AC.take (@assert_iden_spec (Ty.Prod Word256 Word32) term)))))
            (@literal_elements_outpoint_add term))
          (AC.drop (AC.drop (AC.take (@assert_iden_spec Word32 term)))))
        (@literal_ctx8_addn 2 term))
      (AC.drop (AC.drop (AC.drop (@assert_iden_spec (Ty.Sum Ty.Unit Word256) term)))))
    (AC.comp (@literal_bitcoin_annex_hash term) (@literal_ctx8_finalize term)).

Lemma literal_elements_single_input_payload_matches term :
  @literal_elements_single_input_payload term = @elements_single_input_payload_spec term.
Proof.
  unfold literal_elements_single_input_payload, elements_single_input_payload_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_outpoint_add_matches,
    literal_ctx8_addn_algebra_matches, literal_bitcoin_annex_hash_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_single_input_hash {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit Word256) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair (@EFP.Combinators.prim _ _ alg Elements.InputPegin)
      (AC.pair (@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint)
        (AC.pair (@EFP.Combinators.prim _ _ alg Elements.InputSequence)
          (@EFP.Combinators.prim _ _ alg Elements.InputAnnexHash))))
    (AC.case (AC.injl AC.unit) (AC.injr (@literal_elements_single_input_payload term))).

Lemma literal_elements_single_input_hash_matches alg :
  @literal_elements_single_input_hash alg = @elements_single_input_hash_spec alg.
Proof.
  unfold literal_elements_single_input_hash, elements_single_input_hash_spec.
  rewrite literal_elements_single_input_payload_matches. reflexivity.
Qed.

Lemma literal_elements_single_input_hash_parametric :
  EFP.Parametric (@literal_elements_single_input_hash).
Proof.
  intros alg1 alg2 R. rewrite (literal_elements_single_input_hash_matches alg1),
    (literal_elements_single_input_hash_matches alg2).
  exact (elements_single_input_hash_parametric alg1 alg2 R).
Qed.

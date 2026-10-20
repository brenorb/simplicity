(** Original C nonce-hash getter against the canonical primitive-bearing loop.
    Reuse prefix/payload semantics and the native Word256 encoder bridge. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_elements_nonce_hash_spec C.jet_elements_nonces_hash_program.
Require Import C.jet_elements_output_nonce_literal.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal C.jet_sha_tagged_word_spec.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_haskell_word_conversion C.jet_elements_inputs_hash_literal.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_elements_nonce_hash {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_nonce_type) sha256_ctx8_type :=
  I H &&& O H >>> case
    (I H &&& O (@Word.zero 3 (Alg.Assertion.toCore term)) >>> @literal_ctx8_add1 term)
    (I H &&& O (copair
      (O (copair (Alg.scribe (haskell_to_word 3 0x02)) (Alg.scribe (haskell_to_word 3 0x03))) &&& I H)
      ((unit >>> Alg.scribe (haskell_to_word 3 0x01)) &&& iden))
     >>> (O H &&& I O H >>> @literal_ctx8_add1 term) &&& I I H >>> @literal_ctx8_addn 5 term).

Lemma literal_elements_nonce_hash_matches term :
  @literal_elements_nonce_hash term = @elements_nonce_hash_spec term.
Proof.
  unfold literal_elements_nonce_hash, elements_nonce_hash_spec,
    elements_nonce_tag_payload_spec, ctx8_tagged_word_spec,
    nonce_byte_two, nonce_byte_three, byte_one.
  rewrite !haskell_to_word_matches, literal_ctx8_add1_algebra_matches,
    literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_nonce_encode_matches n :
  elements_nonce_encode n = encode_nonce_literal n.
Proof.
  rewrite <- encode_nonce_literal_matches.
  destruct n as [[[odd w] | h] | ]; reflexivity.
Qed.

Definition literal_elements_output_nonces_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @literal_elements_elems_hash elements_nonce_type
    (fun term => @literal_elements_nonce_hash term) 5 term
    (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core
      (@EFP.Combinators.prim _ _ alg Elements.OutputNonce)).

Lemma literal_elements_output_nonces_hash_matches alg :
  @literal_elements_output_nonces_hash alg = @elements_output_nonces_hash_spec alg.
Proof.
  unfold literal_elements_output_nonces_hash, elements_output_nonces_hash_spec.
  rewrite literal_elements_elems_hash_matches.
  unfold jet_sha_hash_elems_reader.hash_elems_spec, jet_sha_hash_loop_gen.gen_loop_run,
    jet_sha_hash_loop_gen.gen_loop_body.
  rewrite literal_elements_nonce_hash_matches. reflexivity.
Qed.

Lemma literal_elements_output_nonces_hash_parametric :
  EFP.Parametric (@literal_elements_output_nonces_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_output_nonces_hash_matches alg1),
    (literal_elements_output_nonces_hash_matches alg2).
  exact (elements_output_nonces_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_output_nonces_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_nonces_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_output_nonces_hash_of 0 56 760)
    (fun a environment => @literal_elements_output_nonces_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_output_nonces_hash_matches.
  exact elements_output_nonces_hash_program_local_spec.
Qed.

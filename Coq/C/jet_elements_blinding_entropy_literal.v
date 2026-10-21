(** Canonical blinding-entropy hashing with its actual Arith.one word8
    program, shared literal SHA operations and the original C cache getter. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_spec C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_elements_blinding_entropy_spec.
Require Import C.jet_elements_blinding_entropy_canonical C.jet_elements_blinding_entropy_hash_program.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_literal C.jet_elements_inputs_hash_literal.
Require Import C.jet_sha_hash_elems_reader C.jet_sha_hash_loop_gen.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_elements_blinding_entropy_absorb {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type blinding_entropy_value_type) sha256_ctx8_type :=
  I H &&& O H >>> case
    (I (iden &&& (unit >>> @Word.zero 3 (Alg.Assertion.toCore term)) >>> @literal_ctx8_add1 term))
    (I (iden &&& (unit >>> @one8_spec (Alg.Assertion.toCore term)) >>> @literal_ctx8_add1 term)
      &&& O H >>> @literal_ctx8_addn 6 term).

Lemma literal_elements_blinding_entropy_absorb_matches term :
  @literal_elements_blinding_entropy_absorb term = @literal_blinding_entropy_hash_spec term.
Proof.
  unfold literal_elements_blinding_entropy_absorb, literal_blinding_entropy_hash_spec.
  rewrite literal_ctx8_add1_algebra_matches, literal_ctx8_addn_algebra_matches.
  reflexivity.
Qed.

Definition literal_elements_issuance_blinding_entropy_hash {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @literal_elements_elems_hash blinding_entropy_value_type
    (fun term => @literal_elements_blinding_entropy_absorb term) 5 term
    (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core (@elements_issuance_blinding_entropy_spec alg)).

Lemma literal_elements_issuance_blinding_entropy_hash_matches alg :
  @literal_elements_issuance_blinding_entropy_hash alg = @literal_issuance_blinding_entropy_hash_spec alg.
Proof.
  unfold literal_elements_issuance_blinding_entropy_hash, literal_issuance_blinding_entropy_hash_spec.
  rewrite literal_elements_elems_hash_matches.
  unfold hash_elems_spec, gen_loop_run, gen_loop_body.
  rewrite literal_elements_blinding_entropy_absorb_matches. reflexivity.
Qed.

Lemma literal_elements_issuance_blinding_entropy_hash_parametric :
  EFP.Parametric (@literal_elements_issuance_blinding_entropy_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_blinding_entropy_hash_matches alg1),
    (literal_elements_issuance_blinding_entropy_hash_matches alg2).
  exact (literal_issuance_blinding_entropy_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuance_blinding_entropy_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_blinding_entropy_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_blinding_entropy_hash_of 0 568 760)
    (fun a environment => @literal_elements_issuance_blinding_entropy_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_issuance_blinding_entropy_hash_matches.
  exact jet_elements_blinding_entropy_canonical.elements_issuance_blinding_entropy_hash_literal_local_spec.
Qed.

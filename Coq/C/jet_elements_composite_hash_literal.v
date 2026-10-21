(** Canonical composite Elements hash programs and complete original C getters.
    Reuse the literal component programs and fixed-vector SHA semantics. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_elements_composite_amounts_hash.
Require Import C.jet_elements_amounts_hash_literal C.jet_elements_nonces_hash_literal C.jet_elements_array_hash_literal.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_elements_fixed_vector_hash (k : nat) {alg : EFP.Algebra}
    (payload : EFP.domain alg Ty.Unit (Vector (Word 3) k)) : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core) payload)
    (@AC.comp _ _ _ core (@literal_ctx8_addn k term) (@literal_ctx8_finalize term)).

Lemma literal_elements_fixed_vector_hash_matches k alg payload :
  @literal_elements_fixed_vector_hash k alg payload = @elements_fixed_vector_hash_spec k alg payload.
Proof.
  unfold literal_elements_fixed_vector_hash, elements_fixed_vector_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_ctx8_addn_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_outputs_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @literal_elements_fixed_vector_hash 7 alg
    (@AC.pair _ _ _ core
      (@AC.pair _ _ _ core (@literal_elements_output_amounts_hash alg) (@literal_elements_output_nonces_hash alg))
      (@AC.pair _ _ _ core (@literal_elements_output_scripts_hash alg) (@literal_elements_output_range_proofs_hash alg))).

Lemma literal_elements_outputs_hash_matches alg :
  @literal_elements_outputs_hash alg = @elements_outputs_hash_spec alg.
Proof.
  unfold literal_elements_outputs_hash, elements_outputs_hash_spec.
  rewrite literal_elements_fixed_vector_hash_matches, literal_elements_output_amounts_hash_matches,
    literal_elements_output_nonces_hash_matches.
  unfold literal_elements_output_scripts_hash, literal_elements_output_range_proofs_hash.
  rewrite !literal_elements_array_hash_matches. reflexivity.
Qed.

Definition literal_elements_input_utxos_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @literal_elements_fixed_vector_hash 6 alg
    (@AC.pair _ _ _ core (@literal_elements_input_amounts_hash alg) (@literal_elements_input_scripts_hash alg)).

Lemma literal_elements_input_utxos_hash_matches alg :
  @literal_elements_input_utxos_hash alg = @elements_input_utxos_hash_spec alg.
Proof.
  unfold literal_elements_input_utxos_hash, elements_input_utxos_hash_spec.
  rewrite literal_elements_fixed_vector_hash_matches, literal_elements_input_amounts_hash_matches.
  unfold literal_elements_input_scripts_hash.
  rewrite literal_elements_array_hash_matches. reflexivity.
Qed.

Lemma literal_elements_outputs_hash_parametric : EFP.Parametric (@literal_elements_outputs_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_outputs_hash_matches alg1), (literal_elements_outputs_hash_matches alg2).
  exact (elements_outputs_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_elements_input_utxos_hash_parametric : EFP.Parametric (@literal_elements_input_utxos_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_input_utxos_hash_matches alg1), (literal_elements_input_utxos_hash_matches alg2).
  exact (elements_input_utxos_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_outputs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_outputs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_outputs_hash_of 0 184 760)
    (fun a environment => @literal_elements_outputs_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_outputs_hash_matches.
  exact elements_outputs_hash_program_local_spec.
Qed.
Theorem elements_input_utxos_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_utxos_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_utxos_hash_of 0 312 760)
    (fun a environment => @literal_elements_input_utxos_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_input_utxos_hash_matches.
  exact elements_input_utxos_hash_program_local_spec.
Qed.

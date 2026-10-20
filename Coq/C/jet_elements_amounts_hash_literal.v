(** Canonical asset/amount serializers and both original C cache getters.
    Reuse the shared prefix/payload absorber, amount pairing and Reader loop. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_elements_amount_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_amounts_hash_program.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal C.jet_sha_tagged_word_spec.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_haskell_word_conversion C.jet_elements_inputs_hash_literal.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_elements_asset_hash {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_asset_hash_type) sha256_ctx8_type :=
  O H &&& I (copair
    (O (copair (Alg.scribe (haskell_to_word 3 0x0a)) (Alg.scribe (haskell_to_word 3 0x0b))) &&& I H)
    ((unit >>> Alg.scribe (haskell_to_word 3 0x01)) &&& iden))
  >>> (O H &&& I O H >>> @literal_ctx8_add1 term) &&& I I H >>> @literal_ctx8_addn 5 term.

Lemma literal_elements_asset_hash_matches term :
  @literal_elements_asset_hash term = @elements_asset_hash_spec term.
Proof.
  unfold literal_elements_asset_hash, elements_asset_hash_spec, asset_tag_payload_spec,
    conf_tag_byte_spec, ctx8_tagged_word_spec, asset_byte_even, asset_byte_odd, byte_one.
  rewrite !haskell_to_word_matches, literal_ctx8_add1_algebra_matches,
    literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Definition literal_elements_amount_hash {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_amount_hash_type) sha256_ctx8_type :=
  I H &&& O H >>> case
    ((I H &&& O O (copair (Alg.scribe (haskell_to_word 3 0x08)) (Alg.scribe (haskell_to_word 3 0x09)))
      >>> @literal_ctx8_add1 term) &&& O I H >>> @literal_ctx8_addn 5 term)
    ((I H &&& (unit >>> Alg.scribe (haskell_to_word 3 0x01)) >>> @literal_ctx8_add1 term)
      &&& O H >>> @literal_ctx8_addn 3 term).

Lemma literal_elements_amount_hash_matches term :
  @literal_elements_amount_hash term = @elements_amount_hash_spec term.
Proof.
  unfold literal_elements_amount_hash, elements_amount_hash_spec, conf_tag_byte_spec,
    amount_byte_even, amount_byte_odd, byte_one.
  rewrite !haskell_to_word_matches, literal_ctx8_add1_algebra_matches,
    !literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Definition literal_elements_asset_amount_hash {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_asset_amount_type) sha256_ctx8_type :=
  (O H &&& I O H >>> @literal_elements_asset_hash term) &&& I I H >>> @literal_elements_amount_hash term.

Lemma literal_elements_asset_amount_hash_matches term :
  @literal_elements_asset_amount_hash term = @elements_asset_amount_hash_spec term.
Proof.
  unfold literal_elements_asset_amount_hash, elements_asset_amount_hash_spec.
  rewrite literal_elements_asset_hash_matches, literal_elements_amount_hash_matches. reflexivity.
Qed.

Definition literal_elements_amounts_hash
    (pm : Elements.t Word32 (Ty.Sum Ty.Unit elements_amount_hash_type))
    (pa : Elements.t Word32 (Ty.Sum Ty.Unit elements_asset_hash_type))
    {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @literal_elements_elems_hash elements_asset_amount_type
    (fun term => @literal_elements_asset_amount_hash term) 5 term
    (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core
      (@elements_amount_pair_spec alg Word32 elements_amount_hash_type elements_asset_hash_type
        (@EFP.Combinators.prim _ _ alg pm) (@EFP.Combinators.prim _ _ alg pa))).

Lemma literal_elements_amounts_hash_matches pm pa alg :
  @literal_elements_amounts_hash pm pa alg = @elements_amounts_hash_spec pm pa alg.
Proof.
  unfold literal_elements_amounts_hash, elements_amounts_hash_spec.
  rewrite literal_elements_elems_hash_matches.
  unfold jet_sha_hash_elems_reader.hash_elems_spec, jet_sha_hash_loop_gen.gen_loop_run,
    jet_sha_hash_loop_gen.gen_loop_body.
  rewrite literal_elements_asset_amount_hash_matches. reflexivity.
Qed.

Definition literal_elements_output_amounts_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_amounts_hash Elements.OutputAmount Elements.OutputAsset alg.
Definition literal_elements_input_amounts_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_amounts_hash Elements.InputAmount Elements.InputAsset alg.

Lemma literal_elements_output_amounts_hash_matches alg :
  @literal_elements_output_amounts_hash alg = @elements_output_amounts_hash_spec alg.
Proof.
  unfold literal_elements_output_amounts_hash, elements_output_amounts_hash_spec.
  apply literal_elements_amounts_hash_matches.
Qed.
Lemma literal_elements_input_amounts_hash_matches alg :
  @literal_elements_input_amounts_hash alg = @elements_input_amounts_hash_spec alg.
Proof.
  unfold literal_elements_input_amounts_hash, elements_input_amounts_hash_spec.
  apply literal_elements_amounts_hash_matches.
Qed.

Lemma literal_elements_output_amounts_hash_parametric :
  EFP.Parametric (@literal_elements_output_amounts_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_output_amounts_hash_matches alg1), (literal_elements_output_amounts_hash_matches alg2).
  exact (elements_amounts_hash_spec_parametric Elements.OutputAmount Elements.OutputAsset alg1 alg2 R).
Qed.
Lemma literal_elements_input_amounts_hash_parametric :
  EFP.Parametric (@literal_elements_input_amounts_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_input_amounts_hash_matches alg1), (literal_elements_input_amounts_hash_matches alg2).
  exact (elements_amounts_hash_spec_parametric Elements.InputAmount Elements.InputAsset alg1 alg2 R).
Qed.

Theorem elements_output_amounts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_output_amounts_hash_of 0 24 760)
    (fun a environment => @literal_elements_output_amounts_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_output_amounts_hash_matches.
  exact elements_output_amounts_hash_program_local_spec.
Qed.
Theorem elements_input_amounts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_amounts_hash_of 0 248 760)
    (fun a environment => @literal_elements_input_amounts_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_input_amounts_hash_matches.
  exact elements_input_amounts_hash_program_local_spec.
Qed.

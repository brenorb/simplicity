(** Canonical literal issuance amount traversals and whole original C getters.
    Reuse the accepted issuance calculations, serializers and generic loop. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_sha_hash_elems_reader C.jet_sha_hash_loop_gen.
Require Import C.jet_elements_issuance_entropy_spec C.jet_elements_issuance_computed_literal.
Require Import C.jet_elements_issuance_amount_hash_spec C.jet_elements_issuance_amounts_hash_program.
Require Import C.jet_elements_amounts_hash_literal C.jet_elements_inputs_hash_literal C.jet_sha_ctx8_literal.
Require Import C.jet_sha256_ctx8_init_spec.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_issuance_asset_amount_absorb {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type issuance_asset_amount_value_type) sha256_ctx8_type :=
  I H &&& O H >>> case
    (I H &&& (unit >>> @Word.zero 4 (Alg.Assertion.toCore term)) >>> @literal_ctx8_addn 1 term)
    (I H &&& (injr (O O H) &&& O I H) >>> @literal_elements_asset_amount_hash term).

Lemma literal_issuance_asset_amount_absorb_matches term :
  @literal_issuance_asset_amount_absorb term = @issuance_asset_amount_absorb_spec term.
Proof.
  unfold literal_issuance_asset_amount_absorb, issuance_asset_amount_absorb_spec.
  rewrite literal_ctx8_addn_algebra_matches, literal_elements_asset_amount_hash_matches.
  reflexivity.
Qed.

Definition literal_elements_issuance_asset_pair {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit issuance_asset_amount_value_type) :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @Alg.Core.Combinators.comp _ _ _ core
    (@Alg.Core.Combinators.pair _ _ _ core (@literal_elements_issuance_asset alg)
      (@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetAmount))
    (@issuance_pair_route core).

Lemma literal_elements_issuance_asset_pair_matches alg :
  @literal_elements_issuance_asset_pair alg =
    @elements_issuance_pair_spec (@elements_issuance_asset_spec) Elements.IssuanceAssetAmount alg.
Proof.
  unfold literal_elements_issuance_asset_pair, elements_issuance_pair_spec.
  rewrite literal_elements_issuance_asset_matches. reflexivity.
Qed.

Definition literal_elements_issuance_token_pair {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit issuance_asset_amount_value_type) :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @Alg.Core.Combinators.comp _ _ _ core
    (@Alg.Core.Combinators.pair _ _ _ core (@literal_elements_issuance_token alg)
      (@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenAmount))
    (@issuance_pair_route core).

Lemma literal_elements_issuance_token_pair_matches alg :
  @literal_elements_issuance_token_pair alg =
    @elements_issuance_pair_spec (@elements_issuance_token_spec) Elements.IssuanceTokenAmount alg.
Proof.
  unfold literal_elements_issuance_token_pair, elements_issuance_pair_spec.
  rewrite literal_elements_issuance_token_matches. reflexivity.
Qed.

Definition literal_elements_issuance_amounts_hash
    (array : forall alg : EFP.Algebra,
      EFP.domain alg Word32 (Ty.Sum Ty.Unit issuance_asset_amount_value_type))
    {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @literal_elements_elems_hash issuance_asset_amount_value_type
    (fun term => @literal_issuance_asset_amount_absorb term) 5 term
    (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core (array alg)).

Definition literal_elements_issuance_asset_amounts_hash {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_issuance_amounts_hash (@literal_elements_issuance_asset_pair) alg.
Definition literal_elements_issuance_token_amounts_hash {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_issuance_amounts_hash (@literal_elements_issuance_token_pair) alg.

Lemma literal_elements_issuance_asset_amounts_hash_matches alg :
  @literal_elements_issuance_asset_amounts_hash alg = @elements_issuance_asset_amounts_hash_spec alg.
Proof.
  unfold literal_elements_issuance_asset_amounts_hash, literal_elements_issuance_amounts_hash,
    elements_issuance_asset_amounts_hash_spec, elements_issuance_amounts_hash_spec.
  rewrite literal_elements_elems_hash_matches.
  unfold hash_elems_spec, gen_loop_run, gen_loop_body.
  rewrite literal_issuance_asset_amount_absorb_matches, literal_elements_issuance_asset_pair_matches.
  reflexivity.
Qed.
Lemma literal_elements_issuance_token_amounts_hash_matches alg :
  @literal_elements_issuance_token_amounts_hash alg = @elements_issuance_token_amounts_hash_spec alg.
Proof.
  unfold literal_elements_issuance_token_amounts_hash, literal_elements_issuance_amounts_hash,
    elements_issuance_token_amounts_hash_spec, elements_issuance_amounts_hash_spec.
  rewrite literal_elements_elems_hash_matches.
  unfold hash_elems_spec, gen_loop_run, gen_loop_body.
  rewrite literal_issuance_asset_amount_absorb_matches, literal_elements_issuance_token_pair_matches.
  reflexivity.
Qed.

Lemma literal_elements_issuance_asset_amounts_hash_parametric :
  EFP.Parametric (@literal_elements_issuance_asset_amounts_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_asset_amounts_hash_matches alg1),
    (literal_elements_issuance_asset_amounts_hash_matches alg2).
  exact (elements_issuance_amounts_hash_spec_parametric (@elements_issuance_asset_spec)
    Elements.IssuanceAssetAmount elements_issuance_asset_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_elements_issuance_token_amounts_hash_parametric :
  EFP.Parametric (@literal_elements_issuance_token_amounts_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_token_amounts_hash_matches alg1),
    (literal_elements_issuance_token_amounts_hash_matches alg2).
  exact (elements_issuance_amounts_hash_spec_parametric (@elements_issuance_token_spec)
    Elements.IssuanceTokenAmount elements_issuance_token_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuance_asset_amounts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_asset_amounts_hash_of 0 472 760)
    (fun a environment => @literal_elements_issuance_asset_amounts_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_issuance_asset_amounts_hash_matches.
  exact elements_issuance_asset_amounts_hash_program_local_spec.
Qed.
Theorem elements_issuance_token_amounts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_token_amounts_hash_of 0 504 760)
    (fun a environment => @literal_elements_issuance_token_amounts_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_issuance_token_amounts_hash_matches.
  exact elements_issuance_token_amounts_hash_program_local_spec.
Qed.

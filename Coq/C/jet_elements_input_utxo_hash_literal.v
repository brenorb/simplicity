(** Whole original Elements input_utxo_hash against the literal primitive-bearing
    SigHash inputUtxoHash program. The initial environment/SHA readiness
    relation and memcpy_model remain explicit caller/library obligations. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_elements_amount_jets C.jet_elements_words_hash_program C.jet_elements_amounts_hash_literal.
Require Import C.jet_elements_input_utxo_hash_spec C.jet_elements_input_utxo_hash_jet.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal.
Require Import C.jet_sha_hash_words_literal C.jet_sha_finalize_literal C.jet_bitcoin_vh_hash_spec.
Require Import C.jet_memcpy_model C.jet_elements_sha_program.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Set Default Timeout 10.

Definition literal_elements_input_utxo_hash {alg : EFP.Algebra} :
    EFP.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@elements_input_amount_spec alg) (@EFP.Combinators.prim _ _ alg Elements.InputScriptHash))
    (@AC.case _ _ _ _ core
      (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.injr _ _ _ core
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core
              (@AC.pair _ _ _ core
                (@AC.comp _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
                (@AC.take _ _ _ core (@AC.iden _ core)))
              (@literal_elements_asset_amount_hash term))
            (@AC.drop _ _ _ core (@assert_iden_spec (Word 8) term)))
          (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term))))).


Lemma literal_elements_input_utxo_hash_matches alg :
  @literal_elements_input_utxo_hash alg = @elements_input_utxo_hash_spec alg.
Proof.
  unfold literal_elements_input_utxo_hash, elements_input_utxo_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_asset_amount_hash_matches,
    literal_ctx8_addn_algebra_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_input_utxo_hash_parametric : EFP.Parametric (@literal_elements_input_utxo_hash).
Proof.
  intros alg1 alg2 R. rewrite (literal_elements_input_utxo_hash_matches alg1),
    (literal_elements_input_utxo_hash_matches alg2).
  exact (elements_input_utxo_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_input_utxo_hash_literal_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_input_utxo_hash elements_ge Elements.env
    Word32 (Ty.Sum Ty.Unit Word256) elements_input_utxo_hash_rep
    (fun a environment => @literal_elements_input_utxo_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_input_utxo_hash_matches.
  rewrite <- elements_sha_genv. exact elements_input_utxo_hash_program_local_spec.
Qed.

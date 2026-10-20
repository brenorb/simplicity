(** Canonical single-input hash program and the original computing C jet.
    Keep the external memcpy model and represented SHA state explicit. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_sha C.jet_sha_linkage C.jet_memcpy_model.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Require Import C.jet_assertion_spec C.jet_sha256_ctx8_init_spec C.jet_bitcoin_vh_hash_spec.
Require Import C.jet_bitcoin_input_hash_spec C.jet_bitcoin_input_hash_jet.
Require Import C.jet_bitcoin_ctx_hash_literal C.jet_bitcoin_inputs_hash_literal.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_bitcoin_assert_iden (B : Ty) {term : Alg.Assertion.Algebra} :
    term (Ty.Sum Ty.Unit B) B :=
  (iden &&& unit) >>>
    @Alg.Assertion.Combinators.assertr Ty.Unit B Ty.Unit B term assertion_cmr_fail0 (O H).

Lemma literal_bitcoin_assert_iden_matches B term :
  @literal_bitcoin_assert_iden B term = @assert_iden_spec B term.
Proof. unfold literal_bitcoin_assert_iden, assert_iden_spec, assert_spec. reflexivity. Qed.

Definition literal_bitcoin_input_hash {alg : PF.Algebra} :
    PF.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.InputPrevOutpoint))
      (@AC.pair _ _ _ core
        (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.InputSequence))
        (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InputAnnexHash))))
    (@AC.case _ _ _ _ core
      (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.injr _ _ _ core
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core
              (@AC.pair _ _ _ core
                (@AC.comp _ _ _ core
                  (@AC.pair _ _ _ core
                    (@AC.comp _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
                    (@AC.take _ _ _ core (@AC.iden _ core)))
                  (@literal_bitcoin_outpoint_hash term))
                (@AC.drop _ _ _ core (@AC.take _ _ _ core (@literal_bitcoin_assert_iden (Word 5) term))))
              (@literal_ctx8_addn 2 term))
            (@AC.drop _ _ _ core (@AC.drop _ _ _ core
              (@literal_bitcoin_assert_iden (Ty.Sum Ty.Unit (Word 8)) term))))
          (@AC.comp _ _ _ core (@literal_bitcoin_annex_hash term) (@literal_ctx8_finalize term))))).

Lemma literal_bitcoin_input_hash_matches alg :
  @literal_bitcoin_input_hash alg = @input_hash_spec alg.
Proof.
  unfold literal_bitcoin_input_hash, input_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_bitcoin_outpoint_hash_algebra_matches,
    !literal_bitcoin_assert_iden_matches, literal_ctx8_addn_algebra_matches,
    literal_bitcoin_annex_hash_algebra_matches, literal_ctx8_finalize_algebra_matches.
  reflexivity.
Qed.

Lemma literal_bitcoin_input_hash_parametric : PF.Parametric (@literal_bitcoin_input_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_bitcoin_input_hash_matches alg1), (literal_bitcoin_input_hash_matches alg2).
  exact (input_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem bitcoin_input_hash_literal_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_bitcoin_input_hash sha_ge ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_hash_rep
    (fun a environment => @literal_bitcoin_input_hash fullalg a environment).
Proof.
  rewrite literal_bitcoin_input_hash_matches. exact bitcoin_input_hash_local_spec.
Qed.

Theorem bitcoin_input_hash_raw_literal_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_bitcoin_input_hash sha_ge raw_bitcoin_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) (raw_env_rep input_hash_rep)
    (fun a environment => @literal_bitcoin_input_hash raw_fullalg a environment).
Proof.
  intro HModel. apply application_raw_program_local_spec_sep.
  - exact literal_bitcoin_input_hash_parametric.
  - exact (bitcoin_input_hash_literal_local_spec HModel).
Qed.

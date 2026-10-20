(** Canonical Elements outpoint/annex/input hash programs and original C
    cache getters. Caller cache construction remains a separate obligation. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_outpoints_hash_program C.jet_elements_annexes_hash_program.
Require Import C.jet_elements_inputs_hash_program C.jet_elements_array_hash_literal.
Require Import C.jet_sha256_ctx8_init_spec C.jet_forWhile_spec C.jet_sha_hash_loop_gen.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Require Import C.jet_bitcoin_ctx_hash_literal C.jet_bitcoin_inputs_hash_literal.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_elements_outpoint_add {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_outpoint_type) sha256_ctx8_type :=
  ((O H &&& I O H >>> @literal_bitcoin_annex_hash term) &&& I I O H
    >>> @literal_ctx8_addn 5 term) &&& I I I H >>> @literal_ctx8_addn 2 term.

Lemma literal_elements_outpoint_add_matches term :
  @literal_elements_outpoint_add term = @elements_outpoint_add_spec term.
Proof.
  unfold literal_elements_outpoint_add, elements_outpoint_add_spec.
  rewrite literal_bitcoin_annex_hash_algebra_matches, !literal_ctx8_addn_algebra_matches.
  reflexivity.
Qed.

Definition literal_elements_outpoints_body {alg : EFP.Algebra} :
    EFP.domain alg (Ty.Prod (Ty.Prod Ty.Unit Word32) sha256_ctx8_type)
      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputPegin)))
      (@AC.pair _ _ _ core
        (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint)))
        (AC.drop AC.iden)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden))
          (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.drop AC.iden))))
        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
          (@AC.injr _ _ _ core (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (AC.drop (AC.drop AC.iden))
              (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden)) (AC.take AC.iden)))
            (@literal_elements_outpoint_add term)))))).

Lemma literal_elements_outpoints_body_matches alg :
  @literal_elements_outpoints_body alg = @elements_outpoints_body alg.
Proof.
  unfold literal_elements_outpoints_body, elements_outpoints_body.
  rewrite literal_elements_outpoint_add_matches. reflexivity.
Qed.

Definition literal_elements_input_outpoints_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
    (@AC.comp _ _ _ core
      (@for_while_program 5 _ _ _ core (@literal_elements_outpoints_body alg))
      (@AC.copair _ _ _ core (@literal_ctx8_finalize term) (@literal_ctx8_finalize term))).

Lemma literal_elements_input_outpoints_hash_matches alg :
  @literal_elements_input_outpoints_hash alg = @elements_input_outpoints_hash_spec alg.
Proof.
  unfold literal_elements_input_outpoints_hash, elements_input_outpoints_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_outpoints_body_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_elems_hash X
    (add : forall term : Alg.Assertion.Algebra,
      term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type) w
    {term : Alg.Assertion.Algebra}
    (array : term (Ty.Prod Ty.Unit (Word w)) (Ty.Sum Ty.Unit X)) : term Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
    (@AC.comp _ _ _ core
      (@for_while_program w Ty.Unit sha256_ctx8_type sha256_ctx8_type core
        (@gen_loop_body X add term Ty.Unit (Word w) array))
      (@AC.copair _ _ _ core (@literal_ctx8_finalize term) (@literal_ctx8_finalize term))).

Lemma literal_elements_elems_hash_matches X add w term array :
  @literal_elements_elems_hash X add w term array = @hash_elems_spec X add w term array.
Proof.
  unfold literal_elements_elems_hash, hash_elems_spec, gen_loop_run.
  rewrite literal_sha_hash_ctx_init_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_input_annexes_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @literal_elements_elems_hash (Ty.Sum Ty.Unit Word256)
    (fun term => @literal_bitcoin_annex_hash term) 5 term
    (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputAnnexHash)).

Lemma literal_elements_input_annexes_hash_matches alg :
  @literal_elements_input_annexes_hash alg = @elements_input_annexes_hash_spec alg.
Proof.
  unfold literal_elements_input_annexes_hash, elements_input_annexes_hash_spec.
  rewrite literal_elements_elems_hash_matches.
  unfold hash_elems_spec, gen_loop_run, gen_loop_body.
  rewrite literal_bitcoin_annex_hash_algebra_matches. reflexivity.
Qed.

Definition literal_elements_inputs_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core)
          (@AC.pair _ _ _ core (@literal_elements_input_outpoints_hash alg)
            (@literal_elements_input_sequences_hash alg)))
        (@literal_ctx8_addn 6 term))
      (@literal_elements_input_annexes_hash alg))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_elements_inputs_hash_matches alg :
  @literal_elements_inputs_hash alg = @elements_inputs_hash_spec alg.
Proof.
  unfold literal_elements_inputs_hash, elements_inputs_hash_spec, literal_elements_input_sequences_hash.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_input_outpoints_hash_matches,
    literal_elements_array_hash_matches, literal_elements_input_annexes_hash_matches,
    !literal_ctx8_addn_algebra_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_input_outpoints_hash_parametric : EFP.Parametric (@literal_elements_input_outpoints_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_input_outpoints_hash_matches alg1), (literal_elements_input_outpoints_hash_matches alg2).
  exact (elements_input_outpoints_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_elements_input_annexes_hash_parametric : EFP.Parametric (@literal_elements_input_annexes_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_input_annexes_hash_matches alg1), (literal_elements_input_annexes_hash_matches alg2).
  exact (elements_input_annexes_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_elements_inputs_hash_parametric : EFP.Parametric (@literal_elements_inputs_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_inputs_hash_matches alg1), (literal_elements_inputs_hash_matches alg2).
  exact (elements_inputs_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_input_outpoints_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_outpoints_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_outpoints_hash_of 0 216 760)
    (fun a environment => @literal_elements_input_outpoints_hash elements_hash_alg a environment).
Proof. rewrite literal_elements_input_outpoints_hash_matches. exact elements_input_outpoints_hash_program_local_spec. Qed.

Theorem elements_input_annexes_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_annexes_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_annexes_hash_of 0 376 760)
    (fun a environment => @literal_elements_input_annexes_hash elements_hash_alg a environment).
Proof. rewrite literal_elements_input_annexes_hash_matches. exact elements_input_annexes_hash_program_local_spec. Qed.

Theorem elements_inputs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_inputs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_inputs_hash_of 0 440 760)
    (fun a environment => @literal_elements_inputs_hash elements_hash_alg a environment).
Proof. rewrite literal_elements_inputs_hash_matches. exact elements_inputs_hash_program_local_spec. Qed.

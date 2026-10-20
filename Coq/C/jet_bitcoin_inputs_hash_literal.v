(** Canonical Bitcoin input-hash programs with the original C cache getters.
    Cache construction and the frozen Bitcoin domain remain separate. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_hash_getter_local.
Require Import C.jet_forWhile_spec C.jet_sha_hash_loop_gen C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_bitcoin_ctx_hash_literal.
Require Import C.jet_haskell_word_conversion.
Require Import C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Require Import C.jet_bitcoin_array_hash_literal.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Lemma literal_bitcoin_outpoint_hash_algebra_matches term :
  @literal_bitcoin_outpoint_hash term = @outpoint_hash_spec term.
Proof.
  unfold literal_bitcoin_outpoint_hash, outpoint_hash_spec.
  rewrite !literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Lemma literal_bitcoin_annex_hash_algebra_matches term :
  @literal_bitcoin_annex_hash term = @annex_hash_spec term.
Proof.
  unfold literal_bitcoin_annex_hash, annex_hash_spec, byte_one.
  rewrite haskell_to_word_matches, literal_ctx8_add1_algebra_matches,
    literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Definition literal_bitcoin_elems_hash X
    (add : forall term : Alg.Assertion.Algebra,
      term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type) w
    (p : BitcoinFull.t (Word w) (Ty.Sum Ty.Unit X))
    {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
    (@AC.comp _ _ _ core
      (@for_while_program w Ty.Unit sha256_ctx8_type sha256_ctx8_type core
        (@gen_loop_body X add term Ty.Unit (Word w)
          (@AC.drop Ty.Unit (Word w) _ core (@PF.Combinators.prim _ _ alg p))))
      (@AC.copair _ _ _ core (@literal_ctx8_finalize term) (@literal_ctx8_finalize term))).

Lemma literal_bitcoin_elems_hash_matches X add w p alg :
  @literal_bitcoin_elems_hash X add w p alg = @elems_hash_spec X add w p alg.
Proof.
  unfold literal_bitcoin_elems_hash, elems_hash_spec, gen_loop_run.
  rewrite literal_sha_hash_ctx_init_matches, literal_ctx8_finalize_algebra_matches.
  reflexivity.
Qed.

Definition literal_bitcoin_input_outpoints_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_elems_hash (Ty.Prod (Word 8) (Word 5))
    (fun term => @literal_bitcoin_outpoint_hash term) 5
    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) alg.

Definition literal_bitcoin_input_annexes_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_elems_hash (Ty.Sum Ty.Unit (Word 8))
    (fun term => @literal_bitcoin_annex_hash term) 5
    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) alg.

Lemma literal_bitcoin_input_outpoints_hash_matches alg :
  @literal_bitcoin_input_outpoints_hash alg = @input_outpoints_hash_spec alg.
Proof.
  unfold literal_bitcoin_input_outpoints_hash, input_outpoints_hash_spec.
  rewrite literal_bitcoin_elems_hash_matches.
  unfold elems_hash_spec, gen_loop_run, gen_loop_body.
  rewrite literal_bitcoin_outpoint_hash_algebra_matches. reflexivity.
Qed.

Lemma literal_bitcoin_input_annexes_hash_matches alg :
  @literal_bitcoin_input_annexes_hash alg = @input_annexes_hash_spec alg.
Proof.
  unfold literal_bitcoin_input_annexes_hash, input_annexes_hash_spec.
  rewrite literal_bitcoin_elems_hash_matches.
  unfold elems_hash_spec, gen_loop_run, gen_loop_body.
  rewrite literal_bitcoin_annex_hash_algebra_matches. reflexivity.
Qed.

Definition literal_bitcoin_inputs_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core)
          (@AC.pair _ _ _ core (@literal_bitcoin_input_outpoints_hash alg)
            (@literal_bitcoin_input_sequences_hash alg)))
        (@literal_ctx8_addn 6 term))
      (@literal_bitcoin_input_annexes_hash alg))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_bitcoin_inputs_hash_matches alg :
  @literal_bitcoin_inputs_hash alg = @inputs_hash_spec alg.
Proof.
  unfold literal_bitcoin_inputs_hash, inputs_hash_spec, literal_bitcoin_input_sequences_hash.
  rewrite literal_sha_hash_ctx_init_matches, literal_bitcoin_input_outpoints_hash_matches,
    literal_bitcoin_array_hash_matches, literal_bitcoin_input_annexes_hash_matches,
    !literal_ctx8_addn_algebra_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_bitcoin_input_outpoints_hash_parametric : PF.Parametric (@literal_bitcoin_input_outpoints_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_bitcoin_input_outpoints_hash_matches alg1),
    (literal_bitcoin_input_outpoints_hash_matches alg2).
  exact (input_outpoints_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_bitcoin_input_annexes_hash_parametric : PF.Parametric (@literal_bitcoin_input_annexes_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_bitcoin_input_annexes_hash_matches alg1),
    (literal_bitcoin_input_annexes_hash_matches alg2).
  exact (input_annexes_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_bitcoin_inputs_hash_parametric : PF.Parametric (@literal_bitcoin_inputs_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_bitcoin_inputs_hash_matches alg1), (literal_bitcoin_inputs_hash_matches alg2).
  exact (inputs_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem bitcoin_input_outpoints_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_outpoints_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep input_outpoints_hash_of 0 112 432)
    (fun a environment => @literal_bitcoin_input_outpoints_hash fullalg a environment).
Proof. rewrite literal_bitcoin_input_outpoints_hash_matches. exact bitcoin_input_outpoints_hash_local_spec. Qed.

Theorem bitcoin_input_annexes_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_annexes_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep input_annexes_hash_of 0 272 432)
    (fun a environment => @literal_bitcoin_input_annexes_hash fullalg a environment).
Proof. rewrite literal_bitcoin_input_annexes_hash_matches. exact bitcoin_input_annexes_hash_local_spec. Qed.

Theorem bitcoin_inputs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_inputs_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep inputs_hash_of 0 336 432)
    (fun a environment => @literal_bitcoin_inputs_hash fullalg a environment).
Proof. rewrite literal_bitcoin_inputs_hash_matches. exact bitcoin_inputs_hash_local_spec. Qed.

Theorem bitcoin_input_outpoints_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_outpoints_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep input_outpoints_hash_of 0 112 432))
    (fun a environment => @literal_bitcoin_input_outpoints_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep; [exact literal_bitcoin_input_outpoints_hash_parametric|].
  exact bitcoin_input_outpoints_hash_literal_local_spec.
Qed.

Theorem bitcoin_input_annexes_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_annexes_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep input_annexes_hash_of 0 272 432))
    (fun a environment => @literal_bitcoin_input_annexes_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep; [exact literal_bitcoin_input_annexes_hash_parametric|].
  exact bitcoin_input_annexes_hash_literal_local_spec.
Qed.

Theorem bitcoin_inputs_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_inputs_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep inputs_hash_of 0 336 432))
    (fun a environment => @literal_bitcoin_inputs_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep; [exact literal_bitcoin_inputs_hash_parametric|].
  exact bitcoin_inputs_hash_literal_local_spec.
Qed.

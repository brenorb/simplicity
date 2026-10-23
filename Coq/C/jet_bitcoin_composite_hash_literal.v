(** Canonical two-component Bitcoin hashes, reusing the literal SHA ports. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_full_prim C.jet_bitcoin_hash_getter_local.
Require Import C.jet_bitcoin_ext_prim.
Require Import C.jet_bitcoin_composite_hash C.jet_bitcoin_array_hash_literal.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Require Import C.jet_sha_hash_words_literal C.jet_sha_ctx8_literal C.jet_sha_finalize_literal.
Require Import C.jet_bitcoin_value_hash_literal.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_bitcoin_pair_hash {alg : PF.Algebra}
    (s t : PF.domain alg Ty.Unit Word256) : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core) (@AC.pair _ _ _ core s t))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 6 term) (@literal_ctx8_finalize term)).

Lemma literal_bitcoin_pair_hash_matches alg s t :
  @literal_bitcoin_pair_hash alg s t = @pair_hash_spec alg s t.
Proof.
  unfold literal_bitcoin_pair_hash, pair_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_ctx8_addn_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_bitcoin_outputs_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_pair_hash alg (@literal_bitcoin_output_values_hash alg)
    (@literal_bitcoin_output_scripts_hash alg).
Definition literal_bitcoin_input_utxos_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_pair_hash alg (@literal_bitcoin_input_values_hash alg)
    (@literal_bitcoin_input_scripts_hash alg).

Lemma literal_bitcoin_outputs_hash_matches alg :
  @literal_bitcoin_outputs_hash alg = @outputs_hash_spec alg.
Proof.
  unfold literal_bitcoin_outputs_hash, outputs_hash_spec.
  rewrite literal_bitcoin_pair_hash_matches, literal_bitcoin_output_values_hash_matches.
  unfold literal_bitcoin_output_scripts_hash.
  rewrite literal_bitcoin_array_hash_matches. reflexivity.
Qed.
Lemma literal_bitcoin_input_utxos_hash_matches alg :
  @literal_bitcoin_input_utxos_hash alg = @input_utxos_hash_spec alg.
Proof.
  unfold literal_bitcoin_input_utxos_hash, input_utxos_hash_spec.
  rewrite literal_bitcoin_pair_hash_matches, literal_bitcoin_input_values_hash_matches.
  unfold literal_bitcoin_input_scripts_hash.
  rewrite literal_bitcoin_array_hash_matches. reflexivity.
Qed.

Lemma literal_bitcoin_outputs_hash_parametric : PF.Parametric (@literal_bitcoin_outputs_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_bitcoin_outputs_hash_matches alg1), (literal_bitcoin_outputs_hash_matches alg2).
  exact (outputs_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_bitcoin_input_utxos_hash_parametric : PF.Parametric (@literal_bitcoin_input_utxos_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_bitcoin_input_utxos_hash_matches alg1), (literal_bitcoin_input_utxos_hash_matches alg2).
  exact (input_utxos_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem bitcoin_outputs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_outputs_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep outputs_hash_of 0 80 432)
    (fun a environment => @literal_bitcoin_outputs_hash fullalg a environment).
Proof. rewrite literal_bitcoin_outputs_hash_matches. exact bitcoin_outputs_hash_local_spec. Qed.
Theorem bitcoin_input_utxos_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_utxos_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep input_utxos_hash_of 0 208 432)
    (fun a environment => @literal_bitcoin_input_utxos_hash fullalg a environment).
Proof. rewrite literal_bitcoin_input_utxos_hash_matches. exact bitcoin_input_utxos_hash_local_spec. Qed.

Theorem bitcoin_outputs_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_outputs_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep outputs_hash_of 0 80 432))
    (fun a environment => @literal_bitcoin_outputs_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact literal_bitcoin_outputs_hash_parametric.
  - exact bitcoin_outputs_hash_literal_local_spec.
Qed.
Theorem bitcoin_input_utxos_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_utxos_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep input_utxos_hash_of 0 208 432))
    (fun a environment => @literal_bitcoin_input_utxos_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact literal_bitcoin_input_utxos_hash_parametric.
  - exact bitcoin_input_utxos_hash_literal_local_spec.
Qed.

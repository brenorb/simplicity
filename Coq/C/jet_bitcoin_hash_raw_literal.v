(** The accepted literal programs interpreted with raw Bitcoin primitives.
    This composes complete original-C contracts with the shared raw-program
    projection. Caller cache construction and frozen-domain limits remain. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_full_prim C.jet_bitcoin_words_hash C.jet_bitcoin_hash_getter_local.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Require Import C.jet_bitcoin_array_hash_literal C.jet_bitcoin_tappath_hash_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_bitcoin_array_hash_parametric k p : PF.Parametric (@literal_bitcoin_array_hash k p).
Proof.
  intros alg1 alg2 R. rewrite !literal_bitcoin_array_hash_matches.
  apply prim_words_hash_spec_parametric.
Qed.

Lemma literal_bitcoin_tappath_hash_parametric : PF.Parametric (@literal_bitcoin_tappath_hash).
Proof.
  intros alg1 alg2 R. rewrite !literal_bitcoin_tappath_hash_matches.
  apply prim_words_hash_spec_parametric.
Qed.

Theorem bitcoin_output_scripts_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_output_scripts_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256
    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 5 (output_scripts_of e)) 0 48 432))
    (fun a environment => @literal_bitcoin_output_scripts_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact (literal_bitcoin_array_hash_parametric _ _).
  - exact bitcoin_output_scripts_hash_literal_local_spec.
Qed.

Theorem bitcoin_input_scripts_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_scripts_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256
    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 5 (input_scripts_of e)) 0 176 432))
    (fun a environment => @literal_bitcoin_input_scripts_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact (literal_bitcoin_array_hash_parametric _ _).
  - exact bitcoin_input_scripts_hash_literal_local_spec.
Qed.

Theorem bitcoin_input_sequences_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_sequences_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256
    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 2 5 (input_sequences_of e)) 0 240 432))
    (fun a environment => @literal_bitcoin_input_sequences_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact (literal_bitcoin_array_hash_parametric _ _).
  - exact bitcoin_input_sequences_hash_literal_local_spec.
Qed.

Theorem bitcoin_input_script_sigs_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sigs_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256
    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 5 (input_script_sigs_of e)) 0 304 432))
    (fun a environment => @literal_bitcoin_input_script_sigs_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact (literal_bitcoin_array_hash_parametric _ _).
  - exact bitcoin_input_script_sigs_hash_literal_local_spec.
Qed.

Theorem bitcoin_tappath_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256
    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176))
    (fun a environment => @literal_bitcoin_tappath_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep.
  - exact literal_bitcoin_tappath_hash_parametric.
  - exact bitcoin_tappath_hash_literal_local_spec.
Qed.

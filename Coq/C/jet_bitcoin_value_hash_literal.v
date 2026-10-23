(** Canonical Bitcoin value-array hash programs against the complete original
    cached C getter calls. Keep the existing frozen base domain and cache
    representation; this module does not establish caller cache construction. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_ext_prim
 C.jet_bitcoin_full_prim C.jet_bitcoin_words_hash C.jet_bitcoin_hash_getter_local
 C.jet_bitcoin_array_hash_literal C.jet_bitcoin_hash_raw_literal C.jet_bitcoin_raw_env
 C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_bitcoin_output_values_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
 @literal_bitcoin_array_hash 3 (BitcoinFull.Base Bitcoin.OutputValue) alg.
Definition literal_bitcoin_input_values_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
 @literal_bitcoin_array_hash 3 (BitcoinFull.Base Bitcoin.InputValue) alg.

Lemma literal_bitcoin_output_values_hash_matches alg :
 @literal_bitcoin_output_values_hash alg=
 @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.OutputValue) alg.
Proof. unfold literal_bitcoin_output_values_hash;apply literal_bitcoin_array_hash_matches. Qed.
Lemma literal_bitcoin_input_values_hash_matches alg :
 @literal_bitcoin_input_values_hash alg=
 @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.InputValue) alg.
Proof. unfold literal_bitcoin_input_values_hash;apply literal_bitcoin_array_hash_matches. Qed.

Lemma literal_bitcoin_output_values_hash_parametric : PF.Parametric (@literal_bitcoin_output_values_hash).
Proof. intros alg1 alg2 R;unfold literal_bitcoin_output_values_hash;apply literal_bitcoin_array_hash_parametric. Qed.
Lemma literal_bitcoin_input_values_hash_parametric : PF.Parametric (@literal_bitcoin_input_values_hash).
Proof. intros alg1 alg2 R;unfold literal_bitcoin_input_values_hash;apply literal_bitcoin_array_hash_parametric. Qed.

Theorem bitcoin_output_values_hash_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_output_values_hash bitcoin_ge ext_environment
 Ty.Unit Word256 (hash_getter_rep (fun e=>words_hash_of 3 5 (output_values_of e)) 0 16 432)
 (fun a environment=>@literal_bitcoin_output_values_hash fullalg a environment).
Proof. rewrite literal_bitcoin_output_values_hash_matches;exact bitcoin_output_values_hash_local_spec. Qed.

Theorem bitcoin_input_values_hash_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_input_values_hash bitcoin_ge ext_environment
 Ty.Unit Word256 (hash_getter_rep (fun e=>words_hash_of 3 5 (input_values_of e)) 0 144 432)
 (fun a environment=>@literal_bitcoin_input_values_hash fullalg a environment).
Proof. rewrite literal_bitcoin_input_values_hash_matches;exact bitcoin_input_values_hash_local_spec. Qed.

Theorem bitcoin_output_values_hash_raw_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_output_values_hash bitcoin_ge raw_bitcoin_environment
 Ty.Unit Word256 (raw_env_rep (hash_getter_rep (fun e=>words_hash_of 3 5 (output_values_of e)) 0 16 432))
 (fun a environment=>@literal_bitcoin_output_values_hash raw_fullalg a environment).
Proof.
 apply application_raw_program_local_spec_sep.
 - exact literal_bitcoin_output_values_hash_parametric.
 - exact bitcoin_output_values_hash_literal_local_spec.
Qed.

Theorem bitcoin_input_values_hash_raw_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_input_values_hash bitcoin_ge raw_bitcoin_environment
 Ty.Unit Word256 (raw_env_rep (hash_getter_rep (fun e=>words_hash_of 3 5 (input_values_of e)) 0 144 432))
 (fun a environment=>@literal_bitcoin_input_values_hash raw_fullalg a environment).
Proof.
 apply application_raw_program_local_spec_sep.
 - exact literal_bitcoin_input_values_hash_parametric.
 - exact bitcoin_input_values_hash_literal_local_spec.
Qed.

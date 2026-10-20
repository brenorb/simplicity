(** Canonical primitive-bearing array hashes and the original cached C getters.
    Cache establishment by the caller and the inherited environment-domain
    boundaries remain separate obligations; no new premise is introduced. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_words_hash.
Require Import C.jet_bitcoin_hash_getter_local C.jet_sha_hash_words_literal.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_bitcoin_array_hash k
    (p : BitcoinFull.t (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  @literal_sha_hash_words k 5 term Ty.Unit
    (@Alg.Core.Combinators.drop Ty.Unit (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) k))
      (Alg.Assertion.toCore term) (@PF.Combinators.prim _ _ alg p)).

Lemma literal_bitcoin_array_hash_matches k p alg :
  @literal_bitcoin_array_hash k p alg = @prim_words_hash_spec k 5 p alg.
Proof.
  unfold literal_bitcoin_array_hash, prim_words_hash_spec.
  rewrite literal_sha_hash_words_matches. reflexivity.
Qed.

Definition literal_bitcoin_output_scripts_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_array_hash 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) alg.
Definition literal_bitcoin_input_scripts_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_array_hash 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) alg.
Definition literal_bitcoin_input_sequences_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_array_hash 2 (BitcoinFull.Base Bitcoin.InputSequence) alg.
Definition literal_bitcoin_input_script_sigs_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  @literal_bitcoin_array_hash 5 (BitcoinFull.Ext BitcoinExt.InputScriptSigHash) alg.

Theorem bitcoin_output_scripts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_output_scripts_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 5 (output_scripts_of e)) 0 48 432)
    (fun a environment => @literal_bitcoin_output_scripts_hash fullalg a environment).
Proof.
  unfold literal_bitcoin_output_scripts_hash. rewrite literal_bitcoin_array_hash_matches.
  exact bitcoin_output_scripts_hash_local_spec.
Qed.

Theorem bitcoin_input_scripts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_scripts_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 5 (input_scripts_of e)) 0 176 432)
    (fun a environment => @literal_bitcoin_input_scripts_hash fullalg a environment).
Proof.
  unfold literal_bitcoin_input_scripts_hash. rewrite literal_bitcoin_array_hash_matches.
  exact bitcoin_input_scripts_hash_local_spec.
Qed.

Theorem bitcoin_input_sequences_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_sequences_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 2 5 (input_sequences_of e)) 0 240 432)
    (fun a environment => @literal_bitcoin_input_sequences_hash fullalg a environment).
Proof.
  unfold literal_bitcoin_input_sequences_hash. rewrite literal_bitcoin_array_hash_matches.
  exact bitcoin_input_sequences_hash_local_spec.
Qed.

Theorem bitcoin_input_script_sigs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sigs_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 5 (input_script_sigs_of e)) 0 304 432)
    (fun a environment => @literal_bitcoin_input_script_sigs_hash fullalg a environment).
Proof.
  unfold literal_bitcoin_input_script_sigs_hash. rewrite literal_bitcoin_array_hash_matches.
  exact bitcoin_input_script_sigs_hash_local_spec.
Qed.

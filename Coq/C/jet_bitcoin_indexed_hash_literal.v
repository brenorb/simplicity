(** Canonical indexed value/script hashes against the original computing jets. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_sha C.jet_sha_linkage C.jet_memcpy_model.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_vh_hash_spec.
Require Import C.jet_bitcoin_output_hash_jet C.jet_bitcoin_input_utxo_hash_jet.
Require Import C.jet_bitcoin_input_hash_literal C.jet_sha_hash_words_literal C.jet_sha_ctx8_literal C.jet_sha_finalize_literal.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_bitcoin_value_script_hash (pv : BitcoinFull.t (Word 5) (Ty.Sum Ty.Unit (Word 6)))
    (ph : BitcoinFull.t (Word 5) (Ty.Sum Ty.Unit (Word 8))) {alg : PF.Algebra} :
    PF.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@PF.Combinators.prim _ _ alg pv) (@PF.Combinators.prim _ _ alg ph))
    (@AC.case _ _ _ _ core
      (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.injr _ _ _ core
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core
              (@AC.pair _ _ _ core
                (@AC.comp _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
                (@AC.take _ _ _ core (@AC.iden _ core)))
              (@literal_ctx8_addn 3 term))
            (@AC.drop _ _ _ core (@literal_bitcoin_assert_iden (Word 8) term)))
          (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term))))).

Lemma literal_bitcoin_value_script_hash_matches pv ph alg :
 @literal_bitcoin_value_script_hash pv ph alg = @vh_hash_spec pv ph alg.
Proof.
 unfold literal_bitcoin_value_script_hash, vh_hash_spec.
 rewrite literal_sha_hash_ctx_init_matches, !literal_ctx8_addn_algebra_matches,
   literal_bitcoin_assert_iden_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_bitcoin_output_hash {alg : PF.Algebra} :
 PF.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
 @literal_bitcoin_value_script_hash (BitcoinFull.Base Bitcoin.OutputValue) (BitcoinFull.Base Bitcoin.OutputScriptHash) alg.

Lemma literal_bitcoin_output_hash_parametric : PF.Parametric (@literal_bitcoin_output_hash).
Proof.
 intros alg1 alg2 R. unfold literal_bitcoin_output_hash.
 rewrite (literal_bitcoin_value_script_hash_matches _ _ alg1),
   (literal_bitcoin_value_script_hash_matches _ _ alg2).
 exact (vh_hash_spec_parametric _ _ alg1 alg2 R).
Qed.

Theorem bitcoin_output_hash_literal_local_spec : memcpy_model ->
 application_jet_local_spec_sep f_simplicity_bitcoin_output_hash sha_ge ext_environment
 (Word 5) (Ty.Sum Ty.Unit (Word 8)) output_hash_rep
 (fun a environment => @literal_bitcoin_output_hash fullalg a environment).
Proof.
 unfold literal_bitcoin_output_hash. rewrite literal_bitcoin_value_script_hash_matches.
 exact bitcoin_output_hash_local_spec.
Qed.

Theorem bitcoin_output_hash_raw_literal_local_spec : memcpy_model ->
 application_jet_local_spec_sep f_simplicity_bitcoin_output_hash sha_ge raw_bitcoin_environment
 (Word 5) (Ty.Sum Ty.Unit (Word 8)) (raw_env_rep output_hash_rep)
 (fun a environment => @literal_bitcoin_output_hash raw_fullalg a environment).
Proof.
 intro HModel. apply application_raw_program_local_spec_sep.
 - exact literal_bitcoin_output_hash_parametric.
 - exact (bitcoin_output_hash_literal_local_spec HModel).
Qed.

Definition literal_bitcoin_input_utxo_hash {alg : PF.Algebra} :
 PF.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
 @literal_bitcoin_value_script_hash (BitcoinFull.Base Bitcoin.InputValue) (BitcoinFull.Ext BitcoinExt.InputScriptHash) alg.

Lemma literal_bitcoin_input_utxo_hash_parametric : PF.Parametric (@literal_bitcoin_input_utxo_hash).
Proof.
 intros alg1 alg2 R. unfold literal_bitcoin_input_utxo_hash.
 rewrite (literal_bitcoin_value_script_hash_matches _ _ alg1),
   (literal_bitcoin_value_script_hash_matches _ _ alg2).
 exact (vh_hash_spec_parametric _ _ alg1 alg2 R).
Qed.

Theorem bitcoin_input_utxo_hash_literal_local_spec : memcpy_model ->
 application_jet_local_spec_sep f_simplicity_bitcoin_input_utxo_hash sha_ge ext_environment
 (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_utxo_hash_rep
 (fun a environment => @literal_bitcoin_input_utxo_hash fullalg a environment).
Proof.
 unfold literal_bitcoin_input_utxo_hash. rewrite literal_bitcoin_value_script_hash_matches.
 exact bitcoin_input_utxo_hash_local_spec.
Qed.

Theorem bitcoin_input_utxo_hash_raw_literal_local_spec : memcpy_model ->
 application_jet_local_spec_sep f_simplicity_bitcoin_input_utxo_hash sha_ge raw_bitcoin_environment
 (Word 5) (Ty.Sum Ty.Unit (Word 8)) (raw_env_rep input_utxo_hash_rep)
 (fun a environment => @literal_bitcoin_input_utxo_hash raw_fullalg a environment).
Proof.
 intro HModel. apply application_raw_program_local_spec_sep.
 - exact literal_bitcoin_input_utxo_hash_parametric.
 - exact (bitcoin_input_utxo_hash_literal_local_spec HModel).
Qed.

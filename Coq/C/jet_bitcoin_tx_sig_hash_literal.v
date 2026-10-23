(** Canonical transaction/signature hash programs with the frozen primitive model.
    The reported LockTime identity difference is not corrected or equated here. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_hash_getter_local.
Require Import C.jet_bitcoin_tx_hash C.jet_bitcoin_sig_all_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_inputs_hash_literal C.jet_bitcoin_composite_hash_literal C.jet_bitcoin_tap_hash_literal.
Require Import C.jet_sha_hash_words_literal C.jet_sha_ctx8_literal C.jet_sha_finalize_literal.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_bitcoin_tx_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core
          (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core)
              (@AC.pair _ _ _ core
                (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.Version))
                (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.LockTime))))
            (@literal_ctx8_addn 3 term))
          (@AC.pair _ _ _ core (@literal_bitcoin_inputs_hash alg) (@literal_bitcoin_outputs_hash alg)))
        (@literal_ctx8_addn 6 term))
      (@literal_bitcoin_input_utxos_hash alg))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_bitcoin_tx_hash_matches alg : @literal_bitcoin_tx_hash alg = @tx_hash_spec alg.
Proof.
 unfold literal_bitcoin_tx_hash, tx_hash_spec.
 rewrite (literal_bitcoin_inputs_hash_matches alg), (literal_bitcoin_outputs_hash_matches alg),
   (literal_bitcoin_input_utxos_hash_matches alg).
 rewrite (literal_sha_hash_ctx_init_matches (Alg.Assertion.toCore (PF.CanonicalStructures.toAssertion alg))).
 rewrite (literal_ctx8_addn_algebra_matches 3 (PF.CanonicalStructures.toAssertion alg)),
   (literal_ctx8_addn_algebra_matches 6 (PF.CanonicalStructures.toAssertion alg)),
   (literal_ctx8_addn_algebra_matches 5 (PF.CanonicalStructures.toAssertion alg)),
   (literal_ctx8_finalize_algebra_matches (PF.CanonicalStructures.toAssertion alg)). reflexivity.
Qed.

Definition literal_bitcoin_sig_all_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core)
          (@AC.pair _ _ _ core (@literal_bitcoin_tx_hash alg) (@literal_bitcoin_tap_env_hash alg)))
        (@literal_ctx8_addn 6 term))
      (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.CurrentIndex)))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 2 term) (@literal_ctx8_finalize term)).

Lemma literal_bitcoin_sig_all_hash_matches alg : @literal_bitcoin_sig_all_hash alg = @sig_all_hash_spec alg.
Proof.
 unfold literal_bitcoin_sig_all_hash, sig_all_hash_spec.
 rewrite (literal_bitcoin_tx_hash_matches alg), (literal_bitcoin_tap_env_hash_matches alg).
 rewrite (literal_sha_hash_ctx_init_matches (Alg.Assertion.toCore (PF.CanonicalStructures.toAssertion alg))).
 rewrite (literal_ctx8_addn_algebra_matches 6 (PF.CanonicalStructures.toAssertion alg)),
   (literal_ctx8_addn_algebra_matches 2 (PF.CanonicalStructures.toAssertion alg)),
   (literal_ctx8_finalize_algebra_matches (PF.CanonicalStructures.toAssertion alg)). reflexivity.
Qed.

Lemma literal_bitcoin_tx_hash_parametric : PF.Parametric (@literal_bitcoin_tx_hash).
Proof.
 intros alg1 alg2 R.
 rewrite (literal_bitcoin_tx_hash_matches alg1), (literal_bitcoin_tx_hash_matches alg2).
 exact (tx_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem bitcoin_tx_hash_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_tx_hash bitcoin_ge ext_environment Ty.Unit Word256
 (hash_getter_rep tx_hash_of 0 368 432) (fun a environment => @literal_bitcoin_tx_hash fullalg a environment).
Proof. rewrite literal_bitcoin_tx_hash_matches. exact bitcoin_tx_hash_local_spec. Qed.

Theorem bitcoin_tx_hash_raw_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_tx_hash bitcoin_ge raw_bitcoin_environment Ty.Unit Word256
 (raw_env_rep (hash_getter_rep tx_hash_of 0 368 432)) (fun a environment => @literal_bitcoin_tx_hash raw_fullalg a environment).
Proof.
 apply application_raw_program_local_spec_sep.
 - exact literal_bitcoin_tx_hash_parametric.
 - exact bitcoin_tx_hash_literal_local_spec.
Qed.

Lemma literal_bitcoin_sig_all_hash_parametric : PF.Parametric (@literal_bitcoin_sig_all_hash).
Proof.
 intros alg1 alg2 R.
 rewrite (literal_bitcoin_sig_all_hash_matches alg1), (literal_bitcoin_sig_all_hash_matches alg2).
 exact (sig_all_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem bitcoin_sig_all_hash_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_sig_all_hash bitcoin_ge ext_environment Ty.Unit Word256
 (env_hash_rep sig_all_hash_of 16) (fun a environment => @literal_bitcoin_sig_all_hash fullalg a environment).
Proof. rewrite literal_bitcoin_sig_all_hash_matches. exact bitcoin_sig_all_hash_local_spec. Qed.

Theorem bitcoin_sig_all_hash_raw_literal_local_spec :
 application_jet_local_spec_sep f_simplicity_bitcoin_sig_all_hash bitcoin_ge raw_bitcoin_environment Ty.Unit Word256
 (raw_env_rep (env_hash_rep sig_all_hash_of 16)) (fun a environment => @literal_bitcoin_sig_all_hash raw_fullalg a environment).
Proof.
 apply application_raw_program_local_spec_sep.
 - exact literal_bitcoin_sig_all_hash_parametric.
 - exact bitcoin_sig_all_hash_literal_local_spec.
Qed.

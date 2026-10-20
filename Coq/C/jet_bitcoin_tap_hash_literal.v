(** Canonical tapleafHash/tapEnvHash programs and original cached C getters.
    Adapt the preserved tapleaf combinator tree to the shared literal SHA and
    fixed-tag host proofs. Final endpoints use raw primitive interpretation. *)
From Coq Require Import ZArith Strings.String.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_hash_getter_local.
Require Import C.jet_bitcoin_tapleaf_hash_spec C.jet_bitcoin_tapleaf_hash_local.
Require Import C.jet_bitcoin_composite_hash C.jet_bitcoin_taproot_literal.
Require Import C.jet_tapdata_literal C.jet_haskell_word_conversion.
Require Import C.jet_buffer_empty_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Require Import C.jet_bitcoin_tappath_hash_literal.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_bitcoin_raw_program.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_sha_tag_ctx (prefix : Ty.tySem (Word 8)) {term : Alg.Core.Algebra} :
    term Ty.Unit sha256_ctx8_type :=
  @buffer_empty_spec (Word 3) 5 Ty.Unit term &&&
    (@literal_tapdata_one64 term &&& Alg.scribe prefix).

Lemma literal_sha_tag_ctx_matches prefix term :
  @literal_sha_tag_ctx prefix term = @ctx8_init_tag_spec prefix term.
Proof.
  unfold literal_sha_tag_ctx, ctx8_init_tag_spec.
  rewrite literal_tapdata_one64_matches. reflexivity.
Qed.

Definition literal_bitcoin_tapleaf_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core
          (@literal_sha_tag_ctx (literal_short_tag_prefix "TapLeaf"%string) core)
          (@AC.pair _ _ _ core
            (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.TapleafVersion))
            (@Alg.scribe Ty.Unit (Word 3) (haskell_to_word 3 32) core)))
        (@literal_ctx8_addn 1 term))
      (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.ScriptCMR)))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_bitcoin_tapleaf_hash_matches alg :
  @literal_bitcoin_tapleaf_hash alg = @tapleaf_hash_spec alg.
Proof.
  unfold literal_bitcoin_tapleaf_hash, tapleaf_hash_spec.
  rewrite literal_sha_tag_ctx_matches, tapleaf_host_prefix_matches, haskell_to_word_matches,
    !literal_ctx8_addn_algebra_matches, literal_ctx8_finalize_algebra_matches.
  reflexivity.
Qed.

Definition literal_bitcoin_tap_env_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core) (@literal_bitcoin_tapleaf_hash alg))
        (@literal_ctx8_addn 5 term))
      (@AC.pair _ _ _ core (@literal_bitcoin_tappath_hash alg)
        (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InternalKey))))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 6 term) (@literal_ctx8_finalize term)).

Lemma literal_bitcoin_tap_env_hash_matches alg :
  @literal_bitcoin_tap_env_hash alg = @tap_env_hash_spec alg.
Proof.
  unfold literal_bitcoin_tap_env_hash, tap_env_hash_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_bitcoin_tapleaf_hash_matches,
    literal_bitcoin_tappath_hash_matches, !literal_ctx8_addn_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_bitcoin_tapleaf_hash_parametric : PF.Parametric (@literal_bitcoin_tapleaf_hash).
Proof.
  intros alg1 alg2 R. rewrite !literal_bitcoin_tapleaf_hash_matches.
  apply tapleaf_hash_spec_parametric.
Qed.
Lemma literal_bitcoin_tap_env_hash_parametric : PF.Parametric (@literal_bitcoin_tap_env_hash).
Proof.
  intros alg1 alg2 R. rewrite !literal_bitcoin_tap_env_hash_matches.
  apply tap_env_hash_spec_parametric.
Qed.

Theorem bitcoin_tapleaf_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tapleaf_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep tapleaf_hash_of 8 8 176)
    (fun a environment => @literal_bitcoin_tapleaf_hash fullalg a environment).
Proof. rewrite literal_bitcoin_tapleaf_hash_matches. exact bitcoin_tapleaf_hash_local_spec. Qed.

Theorem bitcoin_tap_env_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tap_env_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (hash_getter_rep tap_env_hash_of 8 72 176)
    (fun a environment => @literal_bitcoin_tap_env_hash fullalg a environment).
Proof. rewrite literal_bitcoin_tap_env_hash_matches. exact bitcoin_tap_env_hash_local_spec. Qed.

Theorem bitcoin_tapleaf_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tapleaf_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep tapleaf_hash_of 8 8 176))
    (fun a environment => @literal_bitcoin_tapleaf_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep; [exact literal_bitcoin_tapleaf_hash_parametric|].
  exact bitcoin_tapleaf_hash_literal_local_spec.
Qed.

Theorem bitcoin_tap_env_hash_raw_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tap_env_hash bitcoin_ge raw_bitcoin_environment
    Ty.Unit Word256 (raw_env_rep (hash_getter_rep tap_env_hash_of 8 72 176))
    (fun a environment => @literal_bitcoin_tap_env_hash raw_fullalg a environment).
Proof.
  apply application_raw_program_local_spec_sep; [exact literal_bitcoin_tap_env_hash_parametric|].
  exact bitcoin_tap_env_hash_literal_local_spec.
Qed.

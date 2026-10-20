(** Canonical Elements tapleaf/tap-environment programs and original C getters.
    Reuse the fixed short-tag host recipe; caller cache setup stays separate. *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Digest.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_elements_array_hash_literal.
Require Import C.jet_elements_tapleaf_hash_program C.jet_elements_tap_env_hash_program.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_literal C.jet_sha_finalize_literal.
Require Import C.jet_sha_hash_words_literal C.jet_bitcoin_taproot_literal C.jet_bitcoin_tap_hash_literal.
Require Import C.jet_tapdata_host_recipe C.jet_haskell_word_conversion.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma elements_tapleaf_host_blocks :
  List.length (literal_short_tag_bytes "TapLeaf/elements"%string ++ tap_host_pad 16) = 64%nat /\
  List.length (literal_short_tag_digest "TapLeaf/elements"%string ++
    literal_short_tag_digest "TapLeaf/elements"%string) = 64%nat.
Proof. vm_compute; auto. Qed.

Lemma elements_tapleaf_host_serialization :
  literal_short_tag_digest "TapLeaf/elements"%string =
  map (fun b => Int.repr (Byte.unsigned b))
    (hash256_to_bytelist (tap_host_hash (literal_short_tag_state "TapLeaf/elements"%string))).
Proof. vm_compute; reflexivity. Qed.

Lemma elements_tapleaf_host_prefix_matches :
  literal_short_tag_prefix "TapLeaf/elements"%string = elements_tapleaf_prefix.
Proof.
  rewrite literal_short_tag_prefix_words, elements_tapleaf_prefix_matches.
  vm_compute; reflexivity.
Qed.

Definition literal_elements_tapleaf_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core
          (@literal_sha_tag_ctx (literal_short_tag_prefix "TapLeaf/elements"%string) core)
          (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.TapleafVersion)
            (@Alg.scribe Ty.Unit Word8 (haskell_to_word 3 32) core)))
        (@literal_ctx8_addn 1 term))
      (@EFP.Combinators.prim _ _ alg Elements.ScriptCMR))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_elements_tapleaf_hash_matches alg :
  @literal_elements_tapleaf_hash alg = @elements_tapleaf_hash_spec alg.
Proof.
  unfold literal_elements_tapleaf_hash, elements_tapleaf_hash_spec, elements_tapleaf_size.
  rewrite literal_sha_tag_ctx_matches, elements_tapleaf_host_prefix_matches,
    !literal_ctx8_addn_algebra_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Definition literal_elements_tap_env_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core) (@literal_elements_tapleaf_hash alg))
        (@literal_ctx8_addn 5 term))
      (@AC.pair _ _ _ core (@literal_elements_tappath_hash alg)
        (@EFP.Combinators.prim _ _ alg Elements.InternalKey)))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 6 term) (@literal_ctx8_finalize term)).

Lemma literal_elements_tap_env_hash_matches alg :
  @literal_elements_tap_env_hash alg = @elements_tap_env_hash_spec alg.
Proof.
  unfold literal_elements_tap_env_hash, elements_tap_env_hash_spec, literal_elements_tappath_hash.
  rewrite literal_sha_hash_ctx_init_matches, literal_elements_tapleaf_hash_matches,
    literal_elements_array_hash_matches, !literal_ctx8_addn_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_tapleaf_hash_parametric : EFP.Parametric (@literal_elements_tapleaf_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_tapleaf_hash_matches alg1), (literal_elements_tapleaf_hash_matches alg2).
  exact (elements_tapleaf_hash_spec_parametric alg1 alg2 R).
Qed.
Lemma literal_elements_tap_env_hash_parametric : EFP.Parametric (@literal_elements_tap_env_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_tap_env_hash_matches alg1), (literal_elements_tap_env_hash_matches alg2).
  exact (elements_tap_env_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_tapleaf_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tapleaf_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_tapleaf_hash_of 8 8 176)
    (fun a environment => @literal_elements_tapleaf_hash elements_hash_alg a environment).
Proof. rewrite literal_elements_tapleaf_hash_matches. exact elements_tapleaf_hash_program_local_spec. Qed.

Theorem elements_tap_env_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tap_env_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_tap_env_hash_of 8 72 176)
    (fun a environment => @literal_elements_tap_env_hash elements_hash_alg a environment).
Proof. rewrite literal_elements_tap_env_hash_matches. exact elements_tap_env_hash_program_local_spec. Qed.

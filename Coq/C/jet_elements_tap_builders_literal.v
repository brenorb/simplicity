(** Literal Elements taproot builders, reusing the shared tapleaf payload
    and fixed short-tag host recipe. These are whole original C calls. *)
From Coq Require Import ZArith List Strings.String.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_bitcoin_taproot_literal C.jet_haskell_word_conversion C.jet_sha_block_literal C.jet_order_spec.
Require Import C.jet_elements_build_tapleaf_spec C.jet_elements_build_tapbranch_spec C.jet_elements_tap_tags.
Require Import C.jet_elements_build_tapleaf_jet C.jet_elements_build_tapbranch_jet C.jet_elements_tap_contract.
Require Import C.jet_memcpy_model C.jets_elements.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Lemma literal_elements_builder_leaf_prefix_matches :
  literal_short_tag_prefix "TapLeaf/elements"%string = el_tapleaf_prefix.
Proof. rewrite literal_short_tag_prefix_words. vm_compute; reflexivity. Qed.

Lemma literal_elements_builder_branch_prefix_matches :
  literal_short_tag_prefix "TapBranch/elements"%string = el_tapbranch_prefix.
Proof. rewrite literal_short_tag_prefix_words. vm_compute; reflexivity. Qed.

Lemma literal_elements_builder_leaf_block_matches term :
  @literal_build_tapleaf_block term = @el_build_tapleaf_block term.
Proof.
  unfold literal_build_tapleaf_block, el_build_tapleaf_block, el_tl_version, el_tl_w8000, el_tl_len.
  rewrite !haskell_to_word_matches. reflexivity.
Qed.

Definition literal_elements_build_tapleaf {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  (unit >>> Alg.scribe (literal_short_tag_prefix "TapLeaf/elements"%string))
  &&& @literal_build_tapleaf_block term >>> @literal_sha_256_block term.

Lemma literal_elements_build_tapleaf_matches term :
  @literal_elements_build_tapleaf term = @el_build_tapleaf_spec term.
Proof.
  unfold literal_elements_build_tapleaf, el_build_tapleaf_spec.
  rewrite literal_elements_builder_leaf_prefix_matches, literal_elements_builder_leaf_block_matches,
    literal_sha_256_block_core_matches. reflexivity.
Qed.

Definition literal_elements_build_tapbranch {term : Alg.Core.Algebra} : term (Word 9) (Word 8) :=
  ((unit >>> Alg.scribe (literal_short_tag_prefix "TapBranch/elements"%string))
  &&& (@lt_word_spec term 8 &&& iden >>> Bit.cond iden (I H &&& O H))
  >>> @literal_sha_256_block term)
  &&& (unit >>> Alg.scribe (haskell_to_word 9 (2^511+1024))) >>> @literal_sha_256_block term.

Lemma literal_elements_build_tapbranch_matches term :
  @literal_elements_build_tapbranch term = @el_build_tapbranch_spec term.
Proof.
  unfold literal_elements_build_tapbranch, el_build_tapbranch_spec, el_tb_padblock.
  rewrite literal_elements_builder_branch_prefix_matches, haskell_to_word_matches,
    literal_sha_256_block_core_matches. reflexivity.
Qed.

Lemma literal_elements_build_tapleaf_parametric : Alg.Core.Parametric (@literal_elements_build_tapleaf).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_build_tapleaf_matches alg1), (literal_elements_build_tapleaf_matches alg2).
  exact (el_build_tapleaf_spec_parametric alg1 alg2 R).
Qed.

Lemma literal_elements_build_tapbranch_parametric : Alg.Core.Parametric (@literal_elements_build_tapbranch).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_build_tapbranch_matches alg1), (literal_elements_build_tapbranch_matches alg2).
  exact (el_build_tapbranch_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_build_tapleaf_simplicity_literal_local_spec : memcpy_model ->
  elements_sha_local_spec_pre el_sha_tapleaf_pre f_simplicity_build_tapleaf_simplicity
    (Word 8) (Word 8) (@literal_elements_build_tapleaf Alg.CoreFunSem).
Proof. rewrite literal_elements_build_tapleaf_matches. exact elements_build_tapleaf_simplicity_local_spec. Qed.

Theorem elements_build_tapbranch_literal_local_spec : memcpy_model ->
  elements_sha_local_spec_pre el_sha_tapbranch_pre f_simplicity_build_tapbranch
    (Word 9) (Word 8) (@literal_elements_build_tapbranch Alg.CoreFunSem).
Proof. rewrite literal_elements_build_tapbranch_matches. exact elements_build_tapbranch_local_spec. Qed.

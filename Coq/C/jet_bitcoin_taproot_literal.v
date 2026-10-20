(** Canonical Bitcoin TapLeaf/TapBranch builders. Reuse the fixed-block
    host SHA port for the two tag prefixes, and the proved Haskell digest
    decoder. This is not an interpreter for arbitrary host decoders. *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Import C.jet_tapdata_host_recipe C.jet_haskell_hash_word.
Require Import C.jet_haskell_word_conversion C.jet_sha_block_literal C.jet_order_spec.
Require Import C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_build_tapbranch_spec.
Require Import C.jet_bitcoin_tapleaf_hash_spec.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_short_tag_bytes tag :=
  map (fun b => Int.repr (Byte.unsigned b)) (SHA256.str_to_bytes tag).
Definition literal_short_tag_state tag := tap_host_compress tap_host_iv
  (literal_short_tag_bytes tag ++ tap_host_pad (Z.of_nat (String.length tag))).
Definition literal_short_tag_digest tag :=
  flat_map tap_host_put32 (tap_host_state_words (literal_short_tag_state tag)).
Definition literal_short_tag_prefix_state tag := tap_host_compress tap_host_iv
  (literal_short_tag_digest tag ++ literal_short_tag_digest tag).
Definition literal_short_tag_prefix tag := haskell_to_word 8
  (haskell_integer_hash256 (hash256_to_bytelist (tap_host_hash (literal_short_tag_prefix_state tag)))).

Lemma literal_short_tag_prefix_words tag : literal_short_tag_prefix tag =
  from_hash256 (tap_host_hash (literal_short_tag_prefix_state tag)).
Proof. apply haskell_hash_word256. Qed.

Lemma tapleaf_host_blocks :
  List.length (literal_short_tag_bytes "TapLeaf"%string ++ tap_host_pad 7) = 64%nat /\
  List.length (literal_short_tag_digest "TapLeaf"%string ++ literal_short_tag_digest "TapLeaf"%string) = 64%nat.
Proof. vm_compute; auto. Qed.
Lemma tapbranch_host_blocks :
  List.length (literal_short_tag_bytes "TapBranch"%string ++ tap_host_pad 9) = 64%nat /\
  List.length (literal_short_tag_digest "TapBranch"%string ++ literal_short_tag_digest "TapBranch"%string) = 64%nat.
Proof. vm_compute; auto. Qed.
Lemma tapleaf_host_serialization :
  literal_short_tag_digest "TapLeaf"%string =
  map (fun b => Int.repr (Byte.unsigned b))
    (hash256_to_bytelist (tap_host_hash (literal_short_tag_state "TapLeaf"%string))).
Proof. vm_compute; reflexivity. Qed.
Lemma tapbranch_host_serialization :
  literal_short_tag_digest "TapBranch"%string =
  map (fun b => Int.repr (Byte.unsigned b))
    (hash256_to_bytelist (tap_host_hash (literal_short_tag_state "TapBranch"%string))).
Proof. vm_compute; reflexivity. Qed.
Lemma tapleaf_host_prefix_matches : literal_short_tag_prefix "TapLeaf"%string = tapleaf_prefix.
Proof. rewrite literal_short_tag_prefix_words. vm_compute; reflexivity. Qed.
Lemma tapbranch_host_prefix_matches : literal_short_tag_prefix "TapBranch"%string = tapbranch_prefix.
Proof. rewrite literal_short_tag_prefix_words. vm_compute; reflexivity. Qed.

Definition literal_build_tapleaf_block {term : Alg.Core.Algebra} : term (Word 8) (Word 9) :=
  (unit >>> (Alg.scribe (haskell_to_word 3 0xbe) &&& Alg.scribe (haskell_to_word 3 32))) &&& iden
  >>> @Word.full_right_shift1 (Word 4) 4 term
  >>> O H &&& ((((I H &&& (unit >>> Alg.scribe (haskell_to_word 4 0x8000)))
    &&& (unit >>> @Word.zero 5 term)) &&& (unit >>> @Word.zero 6 term))
    &&& (unit >>> Alg.scribe (haskell_to_word 7 (512+16+256)))).

Lemma literal_build_tapleaf_block_matches term :
  @literal_build_tapleaf_block term = @build_tapleaf_block term.
Proof.
  unfold literal_build_tapleaf_block, build_tapleaf_block, tl_version, tl_w8000, tl_len, byte32.
  rewrite !haskell_to_word_matches. reflexivity.
Qed.

Definition literal_build_tapleaf {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  (unit >>> Alg.scribe (literal_short_tag_prefix "TapLeaf"%string))
  &&& @literal_build_tapleaf_block term >>> @literal_sha_256_block term.

Lemma literal_build_tapleaf_matches term : @literal_build_tapleaf term = @build_tapleaf_spec term.
Proof.
  unfold literal_build_tapleaf, build_tapleaf_spec.
  rewrite tapleaf_host_prefix_matches, literal_build_tapleaf_block_matches, literal_sha_256_block_core_matches.
  reflexivity.
Qed.

Definition literal_build_tapbranch {term : Alg.Core.Algebra} : term (Word 9) (Word 8) :=
  ((unit >>> Alg.scribe (literal_short_tag_prefix "TapBranch"%string))
  &&& (@lt_word_spec term 8 &&& iden >>> Bit.cond iden (I H &&& O H))
  >>> @literal_sha_256_block term)
  &&& (unit >>> Alg.scribe (haskell_to_word 9 (2^511+1024))) >>> @literal_sha_256_block term.

Lemma literal_build_tapbranch_matches term : @literal_build_tapbranch term = @build_tapbranch_spec term.
Proof.
  unfold literal_build_tapbranch, build_tapbranch_spec, tb_padblock.
  rewrite tapbranch_host_prefix_matches, haskell_to_word_matches, literal_sha_256_block_core_matches.
  reflexivity.
Qed.

(** Literal Elements calculation programs used by the issuance getters.
    This module bridges programs, not the separate calculate_* C jets. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_elements_issuance_calc_spec C.jet_sha256_iv_init C.jet_sha_block_literal C.jet_haskell_word_conversion.
Module LC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_issuance_iv {core : Alg.Core.Algebra} : core Ty.Unit Word256 :=
  Alg.scribe (haskell_to_word 8
    0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19).

Lemma literal_issuance_iv_matches core : @literal_issuance_iv core = @sha256_iv_spec core.
Proof.
  unfold literal_issuance_iv, sha256_iv_spec.
  rewrite haskell_to_word_matches. reflexivity.
Qed.

Definition literal_issuance_op_hash {core : Alg.Core.Algebra} :
    core (Ty.Prod Word256 Word32) Word256 :=
  LC.comp
    (LC.pair (LC.comp LC.unit literal_issuance_iv)
      (LC.pair
        (LC.comp
          (LC.pair (LC.comp LC.unit literal_issuance_iv)
            (LC.pair (LC.take LC.iden)
              (LC.pair
                (LC.pair
                  (LC.pair
                    (LC.drop (LC.pair
                      (LC.drop (LC.pair (LC.drop LC.iden) (LC.take LC.iden)))
                      (LC.take (LC.pair (LC.drop LC.iden) (LC.take LC.iden)))))
                    (Alg.scribe (haskell_to_word 5 (2 ^ 31))))
                  (LC.comp LC.unit (@Word.zero 6 core)))
                (LC.comp LC.unit (Alg.scribe (haskell_to_word 7 (256 + 32)))))))
          literal_sha_256_block)
        (LC.comp LC.unit (Alg.scribe (haskell_to_word 8 (2 ^ 255 + 256))))))
    literal_sha_256_block.

Lemma literal_issuance_op_hash_matches core : @literal_issuance_op_hash core = @issuance_op_hash_spec core.
Proof.
  unfold literal_issuance_op_hash, issuance_op_hash_spec.
  rewrite !literal_issuance_iv_matches, !literal_sha_256_block_core_matches, !haskell_to_word_matches. reflexivity.
Qed.

Definition literal_calculate_issuance_entropy {core : Alg.Core.Algebra} :
    core (Ty.Prod (Ty.Prod Word256 Word32) Word256) Word256 :=
  LC.comp (LC.pair (LC.comp LC.unit literal_issuance_iv)
    (LC.pair (LC.take literal_issuance_op_hash) (LC.drop LC.iden)))
    literal_sha_256_block.

Lemma literal_calculate_issuance_entropy_matches core : @literal_calculate_issuance_entropy core = @calculate_issuance_entropy_spec core.
Proof.
  unfold literal_calculate_issuance_entropy, calculate_issuance_entropy_spec.
  rewrite !literal_issuance_iv_matches, !literal_sha_256_block_core_matches, literal_issuance_op_hash_matches. reflexivity.
Qed.

Definition literal_calculate_asset {core : Alg.Core.Algebra} : core Word256 Word256 :=
  LC.comp (LC.pair (LC.comp LC.unit literal_issuance_iv)
    (LC.pair LC.iden (LC.comp LC.unit (@Word.zero 8 core))))
    literal_sha_256_block.

Lemma literal_calculate_asset_matches core : @literal_calculate_asset core = @calculate_asset_spec core.
Proof.
  unfold literal_calculate_asset, calculate_asset_spec.
  rewrite !literal_issuance_iv_matches, !literal_sha_256_block_core_matches. reflexivity.
Qed.

Definition literal_calculate_explicit_token {core : Alg.Core.Algebra} : core Word256 Word256 :=
  LC.comp (LC.pair (LC.comp LC.unit literal_issuance_iv)
    (LC.pair LC.iden (LC.comp LC.unit (Alg.scribe (haskell_to_word 8 (2 ^ 248))))))
    literal_sha_256_block.

Lemma literal_calculate_explicit_token_matches core : @literal_calculate_explicit_token core = @calculate_explicit_token_spec core.
Proof.
  unfold literal_calculate_explicit_token, calculate_explicit_token_spec.
  rewrite !literal_issuance_iv_matches, !literal_sha_256_block_core_matches, !haskell_to_word_matches. reflexivity.
Qed.

Definition literal_calculate_confidential_token {core : Alg.Core.Algebra} : core Word256 Word256 :=
  LC.comp (LC.pair (LC.comp LC.unit literal_issuance_iv)
    (LC.pair LC.iden (LC.comp LC.unit (Alg.scribe (haskell_to_word 8 (2 * 2 ^ 248))))))
    literal_sha_256_block.

Lemma literal_calculate_confidential_token_matches core : @literal_calculate_confidential_token core = @calculate_confidential_token_spec core.
Proof.
  unfold literal_calculate_confidential_token, calculate_confidential_token_spec.
  rewrite !literal_issuance_iv_matches, !literal_sha_256_block_core_matches, !haskell_to_word_matches. reflexivity.
Qed.

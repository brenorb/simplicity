(** The bytes actually fed to SHA by the confidential C helpers equal the
    bytes of the canonical assetHash / amountHash Simplicity serializers.
    This is a bridge used by the C execution proof, not a substitute for it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_buffer_input C.jet_read8s_layout.
Require Import C.jet_sha_ctx8_model C.jet_bitcoin_build_tapleaf_spec C.jet_sha_finalize_bridge.
Require Import C.jet_elements_support_sha_be32_write C.jet_elements_support_sha_be64_exec.
Require Import C.jet_elements_confidential_exec C.jet_elements_conf_amount_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.

Lemma elements_hash_words_bytes (h : hash256) :
  be_bytes (hash256_reg h) =
    map word8_array_value (vector_values Word8 5 (from_hash256 h)).
Proof.
  change (jet_sha_be32_write.be_bytes (hash256_reg h) =
    map word8_array_value (vector_values Word8 5 (from_hash256 h))).
  rewrite <- be_bytes_state_regs. f_equal. unfold state_regs.
  rewrite <- hash256_reg_chunks, to_from_hash256. reflexivity.
Qed.

Lemma elements_amount64_bytes (v : int64) :
  c_be64_bytes v =
    map word8_array_value (vector_values Word8 3 (@fromZ (WordToZ 6) (Int64.unsigned v))).
Proof.
  rewrite <- be64_bytes_word, (@to_fromZ (WordToZ 6)).
  change (two_power_nat (bitSize (WordToZ 6))) with Int64.modulus.
  rewrite Z.mod_small by apply Int64.unsigned_range.
  rewrite Int64.repr_unsigned. reflexivity.
Qed.

Lemma elements_asset_canonical_bytes (a : assetWith unit) :
  conf_bytes (Int.repr 10) (Int.repr 11) (conf_prefix a) (asset_words a) =
    map word8_array_value (elements_asset_bytes (encode_asset a)).
Proof.
  destruct a as [h|[odd h] p].
  - change (Int.repr 1 :: be_bytes (hash256_reg h) =
      word8_array_value jet_bitcoin_ctx_hash_spec.byte_one ::
      map word8_array_value (vector_values Word8 5 (from_hash256 h))).
    rewrite elements_hash_words_bytes. reflexivity.
  - destruct odd.
    + change (Int.repr 11 :: be_bytes (hash256_reg h) = word8_array_value asset_byte_odd ::
        map word8_array_value (vector_values Word8 5 (from_hash256 h))).
      rewrite elements_hash_words_bytes. reflexivity.
    + change (Int.repr 10 :: be_bytes (hash256_reg h) = word8_array_value asset_byte_even ::
        map word8_array_value (vector_values Word8 5 (from_hash256 h))).
      rewrite elements_hash_words_bytes. reflexivity.
Qed.

Lemma elements_amount_canonical_bytes (a : amountWith unit) :
  amt_bytes (conf_prefix a) (amount_value a) (amount_words a) =
    map word8_array_value (elements_amount_bytes (encode_amount a)).
Proof.
  destruct a as [v|[odd h] p].
  - change (Int.repr 1 :: c_be64_bytes v =
      word8_array_value jet_bitcoin_ctx_hash_spec.byte_one ::
      map word8_array_value (vector_values Word8 3 (@fromZ (WordToZ 6) (Int64.unsigned v)))).
    rewrite elements_amount64_bytes. reflexivity.
  - destruct odd.
    + change (Int.repr 9 :: be_bytes (hash256_reg h) = word8_array_value amount_byte_odd ::
        map word8_array_value (vector_values Word8 5 (from_hash256 h))).
      rewrite elements_hash_words_bytes. reflexivity.
    + change (Int.repr 8 :: be_bytes (hash256_reg h) = word8_array_value amount_byte_even ::
        map word8_array_value (vector_values Word8 5 (from_hash256 h))).
      rewrite elements_hash_words_bytes. reflexivity.
Qed.

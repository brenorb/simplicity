(** The [sigAllHash] that [simplicity_bitcoin_build_txEnv] stores is the
    canonical [sig_all_hash_of], and the environment assembled by the three
    real builders (transaction, taproot environment, [txEnv]) satisfies the
    cached-hash relations of the accepted hash getters. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_read8s_layout C.jet_word32_chunks C.jet_buffer_input.
Require Import C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_finalize_exec.
Require Import C.jet_sha_be32_write C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_tx_hash C.jet_bitcoin_input_hash_spec C.jet_bitcoin_sig_all_hash.
Require Import C.jet_bitcoin_env_tapenv_tail C.jet_bitcoin_env_tapenv_link.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inexec C.jet_bitcoin_env_tx_link.
Require Import C.jet_bitcoin_env_txenv.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Lemma counter68 : Int64.add (c32 (c32 Int64.zero)) (Int64.repr 4) = Int64.repr 68.
Proof. apply Int64.same_if_eq. vm_compute. reflexivity. Qed.

Lemma be32_bytes_small (N : Z) : 0 <= N <= Int.max_unsigned ->
  c_be32_bytes (Int64.repr N) = map word8_array_value (vector_values (Word 3) 2 (@fromZ (WordToZ 5) N)).
Proof.
  intros HN. rewrite <- (Int.unsigned_repr N) at 1 2 by exact HN. apply be32_bytes_word.
Qed.

Theorem sigall_link (e : ext_environment) :
  Z.of_nat (Bitcoin.envIx (extBase e)) <= Int.max_unsigned ->
  hash256_reg (sig_all_hash_of e) =
    sigall_regs (hash256_reg (tx_hash_of e)) (hash256_reg (tap_env_hash_of e))
      (Int64.repr (Z.of_nat (Bitcoin.envIx (extBase e)))).
Proof.
  intros HIx. unfold sig_all_hash_of, current_index_word. rewrite stream_hash_regs.
  change (vector_values (Word 3) 6 (from_hash256 (tx_hash_of e), from_hash256 (tap_env_hash_of e)))
    with (vector_values (Word 3) 5 (from_hash256 (tx_hash_of e)) ++
          vector_values (Word 3) 5 (from_hash256 (tap_env_hash_of e))).
  rewrite !map_app, !app_length, !vector_values_length.
  unfold sigall_regs. rewrite counter68, !hbytes, be32_bytes_small by lia.
  rewrite <- !ab_app. reflexivity.
Qed.

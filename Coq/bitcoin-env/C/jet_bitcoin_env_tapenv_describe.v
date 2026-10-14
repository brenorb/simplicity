(** [tapenv_describes] is satisfiable for every raw taproot environment: the
    logical environment is built from the bytes the builder read (and any
    transaction-side data), so the hypothesis of
    [mallocTapEnv_cached_hashes] is a definition of the logical environment,
    not an assumption about it. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_word_repr C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_model C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_stream C.jet_bitcoin_env_tapenv_link.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tm_words_length bytes : length (tm_words bytes) = 8%nat.
Proof. reflexivity. Qed.

Lemma state_regs_mk (W : list int) : length W = 8%nat ->
  state_regs (from_hash256 (mk_hash256 W)) = W.
Proof.
  intros HL. unfold state_regs. rewrite <- hash256_reg_chunks, to_from_hash256.
  apply mk_hash256_reg. exact HL.
Qed.

Lemma and254_range (x : int) : 0 <= Int.unsigned (Int.and x (Int.repr 254)) < 256.
Proof.
  pose proof (Int.unsigned_range (Int.and x (Int.repr 254))) as HR.
  pose proof (Int.and_le (Int.repr 254) x) as HL. rewrite Int.and_commut in HL.
  change (Int.unsigned (Int.repr 254)) with 254 in HL. lia.
Qed.

Lemma version_byte (x : int) :
  word8_array_value (@fromZ (WordToZ 3) (Int.unsigned (Int.and x (Int.repr 254)))) = Int.and x (Int.repr 254).
Proof.
  pose proof (and254_range x) as HR. unfold word8_array_value.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  change (2 ^ Z.of_nat (Nat.pow 2 3)) with 256. rewrite Z.mod_small by exact HR.
  apply Int.repr_unsigned.
Qed.

Theorem tapenv_describes_exists (e0 : ext_environment) (nb cb0 : int) (kb cmrb : list int)
    (pb : nat -> list int) :
  0 <= Int.unsigned nb <= 128 ->
  exists e,
    tapenv_describes e nb cb0 kb cmrb pb /\
    Bitcoin.envTx (extBase e) = Bitcoin.envTx (extBase e0) /\
    Bitcoin.envIx (extBase e) = Bitcoin.envIx (extBase e0) /\
    extInScriptHash e = extInScriptHash e0 /\ extInAnnexHash e = extInAnnexHash e0 /\
    extInScriptSigHash e = extInScriptSigHash e0 /\ extTxid e = extTxid e0.
Proof.
  intros HN.
  set (n := Z.to_nat (Int.unsigned nb)).
  set (path := map (fun j => mk_hash256 (tm_words (pb j))) (List.seq 0 n)).
  assert (HPL : (length path <= 128)%nat).
  { unfold path. rewrite map_length, seq_length. unfold n. lia. }
  set (base := @Bitcoin.Build_environment (Bitcoin.envTx (extBase e0)) (Bitcoin.envIx (extBase e0))
                 (mk_hash256 (tm_words cmrb)) (Bitcoin.envIxBounded (extBase e0))).
  exists {| extBase := base;
            extInScriptHash := extInScriptHash e0;
            extInAnnexHash := extInAnnexHash e0;
            extInScriptSigHash := extInScriptSigHash e0;
            extTapleafVersion := Int.unsigned (Int.and cb0 (Int.repr 254));
            extTappath := path;
            extInternalKey := mk_hash256 (tm_words kb);
            extTxid := extTxid e0;
            extInScriptHash_len := extInScriptHash_len e0;
            extInAnnexHash_len := extInAnnexHash_len e0;
            extInScriptSigHash_len := extInScriptSigHash_len e0;
            extTapleafVersion_range := and254_range cb0;
            extTappath_len := HPL |}.
  split; [|repeat split].
  unfold tapenv_describes. cbn [extTapleafVersion extBase Bitcoin.envScriptCMR extTappath extInternalKey]. unfold base. cbn [Bitcoin.envScriptCMR].
  split; [apply version_byte|].
  split; [apply state_regs_mk, tm_words_length|].
  split; [unfold path; rewrite map_length, seq_length; reflexivity|].
  split; [|apply mk_hash256_reg, tm_words_length].
  intros j h Hn. unfold path in Hn. rewrite nth_error_map in Hn.
  destruct (nth_error (List.seq 0 n) j) as [x|] eqn:E; [|discriminate].
  injection Hn as <-.
  assert (Hj : (j < n)%nat).
  { rewrite <- (seq_length n 0). apply nth_error_Some. rewrite E. discriminate. }
  apply (nth_error_nth _ _ 0%nat) in E. rewrite seq_nth in E by exact Hj. cbn in E. subst x.
  symmetry. apply mk_hash256_reg, tm_words_length.
Qed.

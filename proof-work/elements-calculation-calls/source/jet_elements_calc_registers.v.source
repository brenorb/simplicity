(** Representation bridges for the existing C helpers' exact compression
    formulas. These do not establish their linkage or a complete jet call. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Simplicity.SHA256 sha.SHA256.
Require Import C.jet_sha256_iv_init C.jet_elements_issuance_calc_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma issuance_repr_block_pair (h t : Ty.tySem Word256) :
  Simplicity.SHA256.repr_Block (h, t) =
    hash256_reg (to_hash256 h) ++ hash256_reg (to_hash256 t).
Proof.
  destruct h as [[[h0 h1] [h2 h3]] [[h4 h5] [h6 h7]]].
  destruct t as [[[t0 t1] [t2 t3]] [[t4 t5] [t6 t7]]].
  reflexivity.
Qed.

Lemma issuance_iv_registers :
  hash256_reg (to_hash256 (@sha256_iv_spec Alg.CoreFunSem tt)) = sha256_iv_words.
Proof. vm_compute; reflexivity. Qed.

Lemma issuance_compress_registers (h t : Ty.tySem Word256) :
  hash256_reg (to_hash256 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt, (h, t)))) =
  SHA256.hash_block sha256_iv_words
    (hash256_reg (to_hash256 h) ++ hash256_reg (to_hash256 t)).
Proof.
  rewrite Simplicity.SHA256.hashBlock_correct, issuance_repr_block_pair, issuance_iv_registers.
  reflexivity.
Qed.

Lemma issuance_zero_registers :
  hash256_reg (to_hash256 (@Word.zero 8 Alg.CoreFunSem tt)) = repeat Int.zero 8.
Proof. vm_compute; reflexivity. Qed.

Lemma issuance_explicit_token_registers :
  hash256_reg (to_hash256 (@fromZ (WordToZ 8) (2 ^ 248))) =
    Int.repr 16777216 :: repeat Int.zero 7.
Proof. vm_compute; reflexivity. Qed.

Lemma issuance_confidential_token_registers :
  hash256_reg (to_hash256 (@fromZ (WordToZ 8) (2 * 2 ^ 248))) =
    Int.repr 33554432 :: repeat Int.zero 7.
Proof. vm_compute; reflexivity. Qed.

Theorem calculate_asset_registers (h : Ty.tySem Word256) :
  hash256_reg (to_hash256 (@calculate_asset_spec Alg.CoreFunSem h)) =
    SHA256.hash_block sha256_iv_words (hash256_reg (to_hash256 h) ++ repeat Int.zero 8).
Proof.
  change (hash256_reg (to_hash256 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt, (h, @Word.zero 8 Alg.CoreFunSem tt)))) =
    SHA256.hash_block sha256_iv_words (hash256_reg (to_hash256 h) ++ repeat Int.zero 8)).
  rewrite issuance_compress_registers, issuance_zero_registers. reflexivity.
Qed.

Theorem calculate_explicit_token_registers (h : Ty.tySem Word256) :
  hash256_reg (to_hash256 (@calculate_explicit_token_spec Alg.CoreFunSem h)) =
    SHA256.hash_block sha256_iv_words
      (hash256_reg (to_hash256 h) ++ Int.repr 16777216 :: repeat Int.zero 7).
Proof.
  change (hash256_reg (to_hash256 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt, (h, @fromZ (WordToZ 8) (2 ^ 248))))) =
    SHA256.hash_block sha256_iv_words
      (hash256_reg (to_hash256 h) ++ Int.repr 16777216 :: repeat Int.zero 7)).
  rewrite issuance_compress_registers, issuance_explicit_token_registers. reflexivity.
Qed.

Theorem calculate_confidential_token_registers (h : Ty.tySem Word256) :
  hash256_reg (to_hash256 (@calculate_confidential_token_spec Alg.CoreFunSem h)) =
    SHA256.hash_block sha256_iv_words
      (hash256_reg (to_hash256 h) ++ Int.repr 33554432 :: repeat Int.zero 7).
Proof.
  change (hash256_reg (to_hash256 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt, (h, @fromZ (WordToZ 8) (2 * 2 ^ 248))))) =
    SHA256.hash_block sha256_iv_words
      (hash256_reg (to_hash256 h) ++ Int.repr 33554432 :: repeat Int.zero 7)).
  rewrite issuance_compress_registers, issuance_confidential_token_registers. reflexivity.
Qed.

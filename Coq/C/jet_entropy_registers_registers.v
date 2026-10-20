(** Intermediate register bridge for the original entropy C helper. This is
    not itself a helper execution or a complete frame-jet equivalence. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Simplicity.SHA256 sha.SHA256.
Require Import C.jet_sha256_iv_init C.jet_elements_issuance_calc_spec C.jet_elements_calc_registers.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition entropy_swapped_index (x : Ty.tySem Word32) : Ty.tySem Word32 :=
  let '((a, b), (c, d)) := x in ((d, c), (b, a)).

Definition entropy_index_register (x : Ty.tySem Word32) : int :=
  Int.repr (@toZ (WordToZ 5) (entropy_swapped_index x)).

Definition entropy_first_tail (x : Ty.tySem Word32) : Ty.tySem Word256 :=
  (((entropy_swapped_index x, @fromZ (WordToZ 5) (2 ^ 31)), @Word.zero 6 Alg.CoreFunSem tt),
    @fromZ (WordToZ 7) 288).

Lemma entropy_first_tail_registers (x : Ty.tySem Word32) :
  hash256_reg (to_hash256 (entropy_first_tail x)) =
    entropy_index_register x :: Int.repr 2147483648 :: repeat Int.zero 5 ++ [Int.repr 288].
Proof. destruct x as [[a b] [c d]]. reflexivity. Qed.

Lemma entropy_second_tail_registers :
  hash256_reg (to_hash256 (@fromZ (WordToZ 8) (2 ^ 255 + 256))) =
    Int.repr 2147483648 :: repeat Int.zero 6 ++ [Int.repr 256].
Proof. vm_compute; reflexivity. Qed.

Definition entropy_outpoint_registers (txid : list int) (ix : Ty.tySem Word32) : list int :=
  SHA256.hash_block sha256_iv_words
    (SHA256.hash_block sha256_iv_words
      (txid ++ entropy_index_register ix :: Int.repr 2147483648 :: repeat Int.zero 5 ++ [Int.repr 288]) ++
     Int.repr 2147483648 :: repeat Int.zero 6 ++ [Int.repr 256]).

Theorem issuance_outpoint_hash_registers (h : Ty.tySem Word256) (ix : Ty.tySem Word32) :
  hash256_reg (to_hash256 (@issuance_op_hash_spec Alg.CoreFunSem (h, ix))) =
    entropy_outpoint_registers (hash256_reg (to_hash256 h)) ix.
Proof.
  destruct ix as [[a b] [c d]].
  change (hash256_reg (to_hash256 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt,
      (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
        (@sha256_iv_spec Alg.CoreFunSem tt, (h, entropy_first_tail ((a, b), (c, d)))),
       @fromZ (WordToZ 8) (2 ^ 255 + 256))))) =
    entropy_outpoint_registers (hash256_reg (to_hash256 h)) ((a, b), (c, d))).
  rewrite !issuance_compress_registers, entropy_first_tail_registers, entropy_second_tail_registers.
  reflexivity.
Qed.

Theorem calculate_issuance_entropy_registers (h : Ty.tySem Word256)
    (ix : Ty.tySem Word32) (contract : Ty.tySem Word256) :
  hash256_reg (to_hash256 (@calculate_issuance_entropy_spec Alg.CoreFunSem ((h, ix), contract))) =
    SHA256.hash_block sha256_iv_words
      (entropy_outpoint_registers (hash256_reg (to_hash256 h)) ix ++ hash256_reg (to_hash256 contract)).
Proof.
  change (hash256_reg (to_hash256 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt, (@issuance_op_hash_spec Alg.CoreFunSem (h, ix), contract)))) =
    SHA256.hash_block sha256_iv_words
      (entropy_outpoint_registers (hash256_reg (to_hash256 h)) ix ++ hash256_reg (to_hash256 contract))).
  rewrite issuance_compress_registers, issuance_outpoint_hash_registers. reflexivity.
Qed.

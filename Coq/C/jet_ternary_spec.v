(** Canonical Programs.Word.bitwise_tri programs and symbolic machine bridges.
    These supporting lemmas are not, on their own, C jet equivalence proofs. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Arith.
Require Import C.jet_word_repr C.jet_complement_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive ternary_op := TMaj | TXorXor | TCh.
Definition ternary_bool k x y z := match k with
  | TMaj => orb (orb (andb x y) (andb y z)) (andb z x)
  | TXorXor => xorb (xorb x y) z
  | TCh => orb (andb x y) (andb (negb x) z)
  end.
Definition ternary_int64 k x y z := match k with
  | TMaj => Int64.or (Int64.or (Int64.and x y) (Int64.and y z)) (Int64.and z x)
  | TXorXor => Int64.xor (Int64.xor x y) z
  | TCh => Int64.or (Int64.and x y) (Int64.and (Int64.not (Int64.mul Int64.one x)) z)
  end.
Definition ternary_int k x y z := match k with
  | TMaj => Int.or (Int.or (Int.and x y) (Int.and y z)) (Int.and z x)
  | TXorXor => Int.xor (Int.xor x y) z
  | TCh => Int.or (Int.and x y) (Int.and (Int.not (Int.mul Int.one x)) z)
  end.
Definition ternary_bit_spec k {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod Bit (Ty.Prod Bit Bit)) Bit :=
  match k with TMaj => Bit.maj | TXorXor => Bit.xor3 | TCh => Bit.ch end.
(** Word.bitwiseTri/buildBitwiseTri is exactly the Haskell bitwise_tri
    recursion: high triples first, then low triples, with identical routing. *)
Definition ternary_word_spec n k {term : Alg.Core.Algebra} :=
  @Word.bitwiseTri Bit n term (ternary_bit_spec k).

Lemma ternary_word_spec_parametric n k : Alg.Core.Parametric (@ternary_word_spec n k).
Proof.
  intros alg1 alg2 R. unfold ternary_word_spec. apply Word.bitwiseTri_Parametric.
  destruct k; [apply Bit.maj_Parametric|apply Bit.xor3_Parametric|apply Bit.ch_Parametric].
Qed.

Lemma ternary_word_spec_bits n k (x y z : Ty.tySem (Word n)) j :
  Z.testbit (@toZ (WordToZ n) (@ternary_word_spec n k Alg.CoreFunSem (x, (y, z)))) j =
    ternary_bool k (Z.testbit (@toZ (WordToZ n) x) j)
      (Z.testbit (@toZ (WordToZ n) y) j) (Z.testbit (@toZ (WordToZ n) z) j).
Proof.
  unfold ternary_word_spec. apply Word.bitwiseTri_correct.
  - destruct k; reflexivity.
  - intros a b c. destruct k, a as [[]|[]], b as [[]|[]], c as [[]|[]]; reflexivity.
Qed.

Lemma ternary_int64_bits k r t u j : 0 <= j < 64 ->
  Int64.testbit (ternary_int64 k r t u) j =
    ternary_bool k (Int64.testbit r j) (Int64.testbit t j) (Int64.testbit u j).
Proof.
  intros Hj. destruct k; unfold ternary_int64, ternary_bool.
  - rewrite !Int64.bits_or, !Int64.bits_and by exact Hj. reflexivity.
  - rewrite !Int64.bits_xor by exact Hj. reflexivity.
  - rewrite (Int64.mul_commut Int64.one r), Int64.mul_one.
    rewrite Int64.bits_or, !Int64.bits_and, Int64.bits_not by exact Hj. reflexivity.
Qed.
Lemma ternary_int_bits k r t u j : 0 <= j < 32 ->
  Int.testbit (ternary_int k r t u) j =
    ternary_bool k (Int.testbit r j) (Int.testbit t j) (Int.testbit u j).
Proof.
  intros Hj. destruct k; unfold ternary_int, ternary_bool.
  - rewrite !Int.bits_or, !Int.bits_and by exact Hj. reflexivity.
  - rewrite !Int.bits_xor by exact Hj. reflexivity.
  - rewrite (Int.mul_commut Int.one r), Int.mul_one.
    rewrite Int.bits_or, !Int.bits_and, Int.bits_not by exact Hj. reflexivity.
Qed.

Lemma ternary_int64_denotes n k (x y z : Ty.tySem (Word n)) r t u :
  two_power_nat n <= 64 -> Int64.unsigned r = @toZ (WordToZ n) x ->
  Int64.unsigned t = @toZ (WordToZ n) y -> Int64.unsigned u = @toZ (WordToZ n) z ->
  @fromZ (WordToZ n) (Int64.unsigned (ternary_int64 k r t u)) =
    @ternary_word_spec n k Alg.CoreFunSem (x, (y, z)).
Proof.
  intros Hwidth Hr Ht Hu. apply word_fromZ_bits. intros j Hj. rewrite word_width_power in Hj.
  change (Int64.testbit (ternary_int64 k r t u) j =
    Z.testbit (@toZ (WordToZ n) (@ternary_word_spec n k Alg.CoreFunSem (x, (y, z)))) j).
  rewrite ternary_int64_bits by lia. unfold Int64.testbit. rewrite Hr, Ht, Hu.
  symmetry. apply ternary_word_spec_bits.
Qed.
Lemma ternary_int_denotes n k (x y z : Ty.tySem (Word n)) r t u :
  two_power_nat n <= 32 -> Int.unsigned r = @toZ (WordToZ n) x ->
  Int.unsigned t = @toZ (WordToZ n) y -> Int.unsigned u = @toZ (WordToZ n) z ->
  @fromZ (WordToZ n) (Int.unsigned (ternary_int k r t u)) =
    @ternary_word_spec n k Alg.CoreFunSem (x, (y, z)).
Proof.
  intros Hwidth Hr Ht Hu. apply word_fromZ_bits. intros j Hj. rewrite word_width_power in Hj.
  change (Int.testbit (ternary_int k r t u) j =
    Z.testbit (@toZ (WordToZ n) (@ternary_word_spec n k Alg.CoreFunSem (x, (y, z)))) j).
  rewrite ternary_int_bits by lia. unfold Int.testbit. rewrite Hr, Ht, Hu.
  symmetry. apply ternary_word_spec_bits.
Qed.

(** Exact Programs.Word.bitwise_bin recursion and canonical and/or/xor bits.
    Symbolic bridges below are used by the actual generated jet call proofs. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Arith.
Require Import C.jet_word_repr C.jet_complement_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Notation "s &&* t" := (Alg.Core.Combinators.pair s t) (at level 70, right associativity).
Local Notation "s >>* t" := (Alg.Core.Combinators.comp s t) (at level 90, right associativity).
Local Notation "'H'" := Alg.Core.Combinators.iden.
Local Notation "'O' x" := (Alg.Core.Combinators.take x) (at level 0, right associativity).
Local Notation "'I' x" := (Alg.Core.Combinators.drop x) (at level 0, right associativity).

Inductive binary_op := BAnd | BOr | BXor.
Definition binary_bool k := match k with BAnd => andb | BOr => orb | BXor => xorb end.
Definition binary_int64 k := match k with BAnd => Int64.and | BOr => Int64.or | BXor => Int64.xor end.
Definition binary_int k := match k with BAnd => Int.and | BOr => Int.or | BXor => Int.xor end.

Definition binary_bit_spec k {term : Alg.Core.Algebra} : @Alg.Core.domain term (Ty.Prod Bit Bit) Bit :=
  match k with
  | BAnd => Bit.and (O H) (I H)
  | BOr => Bit.or (O H) (I H)
  | BXor => (O H) &&* H >>* Bit.cond (Bit.not (I H)) (I H)
  end.

Fixpoint binary_word_spec n k {term : Alg.Core.Algebra} : @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) (Word n) :=
  match n with
  | 0%nat => binary_bit_spec k
  | S n => (O O H &&* I O H >>* binary_word_spec n k)
       &&* (O I H &&* I I H >>* binary_word_spec n k)
  end.

Lemma binary_word_spec_parametric n k : Alg.Core.Parametric (@binary_word_spec n k).
Proof.
  intros alg1 alg2 R. induction n; cbn [binary_word_spec].
  - unfold binary_bit_spec. destruct k.
    + apply Bit.and_Parametric;
        [apply Alg.take_Parametric|apply Alg.drop_Parametric]; apply Alg.iden_Parametric.
    + apply Bit.or_Parametric;
        [apply Alg.take_Parametric|apply Alg.drop_Parametric]; apply Alg.iden_Parametric.
    + apply Alg.comp_Parametric.
      * apply Alg.pair_Parametric.
        -- apply Alg.take_Parametric. apply Alg.iden_Parametric.
        -- apply Alg.iden_Parametric.
      * apply Bit.cond_Parametric.
        -- apply Bit.not_Parametric. apply Alg.drop_Parametric. apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric. apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric; apply Alg.comp_Parametric.
    all: try exact IHn.
    all: apply Alg.pair_Parametric.
    all: first [apply Alg.take_Parametric|apply Alg.drop_Parametric].
    all: first [apply Alg.take_Parametric|apply Alg.drop_Parametric].
    all: apply Alg.iden_Parametric.
Qed.

Lemma binary_word_spec_bits n k (x y : Ty.tySem (Word n)) j :
  0 <= j < two_power_nat n ->
  Z.testbit (@toZ (WordToZ n) (@binary_word_spec n k Alg.CoreFunSem (x, y))) j =
    binary_bool k (Z.testbit (@toZ (WordToZ n) x) j) (Z.testbit (@toZ (WordToZ n) y) j).
Proof.
  revert x y j. induction n as [|n IH]; intros x y j Hj.
  - change (0 <= j < 1) in Hj. assert (j = 0) by lia. subst j.
    destruct k, x as [[]|[]], y as [[]|[]]; reflexivity.
  - destruct x as [xh xl], y as [yh yl].
    change (Z.testbit (@toZ (WordToZ (S n))
      (@binary_word_spec n k Alg.CoreFunSem (xh, yh), @binary_word_spec n k Alg.CoreFunSem (xl, yl))) j =
      binary_bool k (Z.testbit (@toZ (WordToZ (S n)) (xh, xl)) j)
        (Z.testbit (@toZ (WordToZ (S n)) (yh, yl)) j)).
    rewrite two_power_nat_S in Hj.
    destruct (Z_lt_le_dec j (two_power_nat n)) as [Hlo|Hhi].
    + rewrite !testbitToZLo by exact Hlo. apply IH. lia.
    + rewrite !testbitToZHi by exact Hhi. apply IH. lia.
Qed.

Lemma binary_int64_bits k r s j : 0 <= j < 64 ->
  Int64.testbit (binary_int64 k r s) j = binary_bool k (Int64.testbit r j) (Int64.testbit s j).
Proof. intros Hj. destruct k; [apply Int64.bits_and|apply Int64.bits_or|apply Int64.bits_xor]; exact Hj. Qed.
Lemma binary_int_bits k r s j : 0 <= j < 32 ->
  Int.testbit (binary_int k r s) j = binary_bool k (Int.testbit r j) (Int.testbit s j).
Proof. intros Hj. destruct k; [apply Int.bits_and|apply Int.bits_or|apply Int.bits_xor]; exact Hj. Qed.

Lemma binary_int64_denotes n k (x y : Ty.tySem (Word n)) r s :
  two_power_nat n <= 64 -> Int64.unsigned r = @toZ (WordToZ n) x ->
  Int64.unsigned s = @toZ (WordToZ n) y ->
  @fromZ (WordToZ n) (Int64.unsigned (binary_int64 k r s)) = @binary_word_spec n k Alg.CoreFunSem (x, y).
Proof.
  intros Hwidth Hr Hs. apply word_fromZ_bits. intros j Hj. rewrite word_width_power in Hj.
  change (Int64.testbit (binary_int64 k r s) j =
    Z.testbit (@toZ (WordToZ n) (@binary_word_spec n k Alg.CoreFunSem (x, y))) j).
  rewrite binary_int64_bits by lia. unfold Int64.testbit. rewrite Hr, Hs.
  symmetry. apply binary_word_spec_bits; exact Hj.
Qed.

Lemma binary_int_denotes n k (x y : Ty.tySem (Word n)) r s :
  two_power_nat n <= 32 -> Int.unsigned r = @toZ (WordToZ n) x ->
  Int.unsigned s = @toZ (WordToZ n) y ->
  @fromZ (WordToZ n) (Int.unsigned (binary_int k r s)) = @binary_word_spec n k Alg.CoreFunSem (x, y).
Proof.
  intros Hwidth Hr Hs. apply word_fromZ_bits. intros j Hj. rewrite word_width_power in Hj.
  change (Int.testbit (binary_int k r s) j =
    Z.testbit (@toZ (WordToZ n) (@binary_word_spec n k Alg.CoreFunSem (x, y))) j).
  rewrite binary_int_bits by lia. unfold Int.testbit. rewrite Hr, Hs.
  symmetry. apply binary_word_spec_bits; exact Hj.
Qed.

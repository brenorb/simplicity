(** Exact recursion of Programs.Word.complement in the CoreJets catalog.
    The bit lemmas are representation bridges for the C execution proofs. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Arith.
Require Import C.jet_word_repr.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint complement_spec n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) (Word n) :=
  match n with
  | O => @Bit.not Bit term (@Alg.Core.Combinators.iden Bit term)
  | S n => @Alg.Core.Combinators.pair (Word (S n)) (Word n) (Word n) term
      (@Alg.Core.Combinators.take (Word n) (Word n) (Word n) term (complement_spec n))
      (@Alg.Core.Combinators.drop (Word n) (Word n) (Word n) term (complement_spec n))
  end.

Lemma complement_spec_parametric n : Alg.Core.Parametric (@complement_spec n).
Proof.
  intros alg1 alg2 R. induction n; cbn [complement_spec].
  - apply Bit.not_Parametric. apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.take_Parametric. exact IHn.
    + apply Alg.drop_Parametric. exact IHn.
Qed.

Lemma word_width_power n : Z.of_nat (Nat.pow 2 n) = two_power_nat n.
Proof. rewrite two_power_nat_equiv, Nat2Z.inj_pow. reflexivity. Qed.

Lemma complement_spec_bits n (x : Ty.tySem (Word n)) j :
  0 <= j < two_power_nat n ->
  Z.testbit (@toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem x)) j =
    negb (Z.testbit (@toZ (WordToZ n) x) j).
Proof.
  revert x j. induction n as [|n IH]; intros x j Hj.
  - change (0 <= j < 1) in Hj. assert (j = 0) by lia. subst j.
    destruct x as [[]|[]]; reflexivity.
  - destruct x as [hi lo].
    change (Z.testbit (@toZ (WordToZ (S n))
      (@complement_spec n Alg.CoreFunSem hi, @complement_spec n Alg.CoreFunSem lo)) j =
      negb (Z.testbit (@toZ (WordToZ (S n)) (hi, lo)) j)).
    rewrite two_power_nat_S in Hj.
    destruct (Z_lt_le_dec j (two_power_nat n)) as [Hlo|Hhi].
    + rewrite !testbitToZLo by exact Hlo. apply IH. lia.
    + rewrite !testbitToZHi by exact Hhi. apply IH. lia.
Qed.

Lemma complement_int64_denotes n (x : Ty.tySem (Word n)) r :
  two_power_nat n <= 64 -> Int64.unsigned r = @toZ (WordToZ n) x ->
  @fromZ (WordToZ n) (Int64.unsigned (Int64.not r)) = @complement_spec n Alg.CoreFunSem x.
Proof.
  intros Hwidth Hr. apply word_fromZ_bits. intros j Hj. rewrite word_width_power in Hj.
  change (Int64.testbit (Int64.not r) j =
    Z.testbit (@toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem x)) j).
  rewrite Int64.bits_not by (change Int64.zwordsize with 64; lia).
  unfold Int64.testbit. rewrite Hr. symmetry. apply complement_spec_bits; exact Hj.
Qed.

Lemma complement_int_denotes n (x : Ty.tySem (Word n)) r :
  two_power_nat n <= 32 -> Int.unsigned r = @toZ (WordToZ n) x ->
  @fromZ (WordToZ n) (Int.unsigned (Int.not r)) = @complement_spec n Alg.CoreFunSem x.
Proof.
  intros Hwidth Hr. apply word_fromZ_bits. intros j Hj. rewrite word_width_power in Hj.
  change (Int.testbit (Int.not r) j =
    Z.testbit (@toZ (WordToZ n) (@complement_spec n Alg.CoreFunSem x)) j).
  rewrite Int.bits_not by (change Int.zwordsize with 32; lia).
  unfold Int.testbit. rewrite Hr. symmetry. apply complement_spec_bits; exact Hj.
Qed.

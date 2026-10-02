(** Literal canonical Programs.Arith.multiply, with symbolic carrier bridges.
    These are specification/representation lemmas, not public jet coverage. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word C.jet_word_repr C.jet_toZ.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition multiply_word_spec n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) (Word (S n)) :=
  Alg.Core.Combinators.comp
    (Alg.Core.Combinators.pair Alg.Core.Combinators.iden
      (Alg.Core.Combinators.comp Alg.Core.Combinators.unit (@zero (S n) term)))
    (@fullMultiplier n term).

Lemma multiply_word_spec_parametric n : Alg.Core.Parametric (@multiply_word_spec n).
Proof.
  intros alg1 alg2 R. unfold multiply_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.iden_Parametric|].
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply zero_Parametric].
  - apply fullMultiplier_Parametric.
Qed.

Lemma multiply_word_spec_numeric n (x y : Ty.tySem (Word n)) :
  @toZ (WordToZ (S n)) (@multiply_word_spec n Alg.CoreFunSem (x, y)) =
    @toZ (WordToZ n) x * @toZ (WordToZ n) y.
Proof.
  change (@toZ (WordToZ (S n)) (@multiplier n Alg.CoreFunSem (x, y)) =
    @toZ (WordToZ n) x * @toZ (WordToZ n) y).
  apply multiplier_correct.
Qed.

Lemma multiply_int64_denotes n (x y : Ty.tySem (Word n)) r t :
  Z.of_nat (Nat.pow 2 (S n)) <= 64 ->
  Int64.unsigned r = @toZ (WordToZ n) x ->
  Int64.unsigned t = @toZ (WordToZ n) y ->
  @fromZ (WordToZ (S n)) (Int64.unsigned (Int64.mul r t)) =
    @multiply_word_spec n Alg.CoreFunSem (x, y).
Proof.
  intros Hwidth Hr Ht.
  pose proof (word_toZ_range (S n) (@multiply_word_spec n Alg.CoreFunSem (x, y))) as Hrange.
  rewrite multiply_word_spec_numeric in Hrange.
  assert (Hlimit : 2 ^ Z.of_nat (Nat.pow 2 (S n)) <= Int64.modulus).
  { change Int64.modulus with (2 ^ 64). apply Z.pow_le_mono_r; lia. }
  unfold Int64.mul. rewrite Int64.unsigned_repr_eq, Hr, Ht.
  rewrite Z.mod_small by lia. rewrite <- multiply_word_spec_numeric. apply from_toZ.
Qed.

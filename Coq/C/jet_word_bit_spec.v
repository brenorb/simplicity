(** Reusable Simplicity projection of one bit, indexed least-significant first.
    Concrete canonical projection paths are related to this shared term by
    structural equality. This is representation infrastructure, not jet coverage. *)
From Coq Require Import ZArith Lia Bool.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit C.jet_word_repr.
Module BC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint word_bit_spec n i {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) Bit :=
  match n as k return @Alg.Core.domain term (Word k) Bit with
  | O => BC.iden
  | S k => if Nat.ltb i (Nat.pow 2 k)
      then BC.drop (@word_bit_spec k i term)
      else BC.take (@word_bit_spec k (i - Nat.pow 2 k)%nat term)
  end.

Lemma word_bit_spec_parametric n i : Alg.Core.Parametric (@word_bit_spec n i).
Proof.
  revert i. induction n as [|n IH]; intros i alg1 alg2 R.
  - apply Alg.iden_Parametric.
  - cbn [word_bit_spec]. destruct (Nat.ltb i (Nat.pow 2 n));
      [apply Alg.drop_Parametric|apply Alg.take_Parametric]; apply IH.
Qed.

Lemma word_count_power n : two_power_nat n = Z.of_nat (Nat.pow 2 n).
Proof. rewrite <- bitSize_Word, word_bitSize. reflexivity. Qed.

Lemma word_bit_spec_numeric n i (x : Ty.tySem (Word n)) :
  (i < Nat.pow 2 n)%nat ->
  Bit.toBool (@word_bit_spec n i Alg.CoreFunSem x) =
    Z.testbit (@toZ (WordToZ n) x) (Z.of_nat i).
Proof.
  revert i x. induction n as [|n IH]; intros i x Hi.
  - assert (i = O) by (cbn in Hi; lia). subst i.
    destruct x as [u | u]; destruct u; reflexivity.
  - destruct x as [hi lo]. cbn [word_bit_spec].
    destruct (Nat.ltb i (Nat.pow 2 n)) eqn:Hhalf.
    + apply Nat.ltb_lt in Hhalf.
      change (Bit.toBool (@word_bit_spec n i Alg.CoreFunSem lo) =
        Z.testbit (@toZ (WordToZ (S n)) (hi, lo)) (Z.of_nat i)).
      rewrite testbitToZLo by (rewrite word_count_power; lia). apply IH; exact Hhalf.
    + apply Nat.ltb_ge in Hhalf.
      change (Bit.toBool (@word_bit_spec n (i - Nat.pow 2 n)%nat Alg.CoreFunSem hi) =
        Z.testbit (@toZ (WordToZ (S n)) (hi, lo)) (Z.of_nat i)).
      rewrite testbitToZHi by (rewrite word_count_power; lia).
      rewrite word_count_power, <- Nat2Z.inj_sub by exact Hhalf.
      apply IH. cbn in Hi. lia.
Qed.

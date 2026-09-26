(** Symbolic arithmetic bridge for the canonical Simplicity increment_64 jet. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Arith.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec C.jet_increment_wide_word.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition increment64_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 6) (Ty.Prod Bit (Word 6)) :=
  @increment_word_spec term 6.

Definition increment64_spec_value :
    Ty.tySem (Word 6) -> Ty.tySem (Ty.Prod Bit (Word 6)) :=
  @increment64_spec Alg.CoreFunSem.

Definition increment64_carry (r : int64) : bool :=
  Int64.ltu (Int64.repr (Int64.max_unsigned - 1)) r.

Definition increment64_payload (r : int64) : int64 := Int64.add r Int64.one.

Lemma increment64_carry_is_overflow r :
  increment64_carry r = Datatypes.true <->
  Int64.unsigned r = Int64.max_unsigned.
Proof.
  unfold increment64_carry, Int64.ltu.
  assert (Hws : Int64.zwordsize = 64) by reflexivity.
  pose proof Int64.wordsize_max_unsigned as HM.
  rewrite Int64.unsigned_repr by
    (rewrite Hws in HM; lia).
  destruct (zlt (Int64.max_unsigned - 1) (Int64.unsigned r)) as [Hlt|Hge].
  -
    pose proof (Int64.unsigned_range r) as HR.
    split; [intros _; unfold Int64.max_unsigned in *; lia|intros _; reflexivity].
  - split; [discriminate|intros Heq; lia].
Qed.

Lemma increment64_values_denote_spec r :
  ((if increment64_carry r then inr tt else inl tt),
    decode_wide W64 (increment64_payload r)) =
  increment64_spec_value (@fromZ (WordToZ 6) (Int64.unsigned r)).
Proof.
  pose proof (Int64.unsigned_range r) as Hr.
  pose proof (Int64.unsigned_add_either r Int64.one) as Hadd.
  rewrite Int64.unsigned_one in Hadd.
  assert (HM : Int64.modulus = 18446744073709551616) by reflexivity.
  rewrite HM in Hr, Hadd.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 6))).
  unfold increment64_spec_value, increment64_spec.
  rewrite increment_word_spec_fun, Word.fullAdder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 6)).
  unfold increment64_payload, decode_wide.
  rewrite !(@to_fromZ (WordToZ 6)), Word.zero_correct.
  assert (Hpow : two_power_nat (bitSize (WordToZ 6)) = Int64.modulus)
    by reflexivity.
  rewrite Hpow, HM in *.
  rewrite (Z.mod_small (Int64.unsigned r) 18446744073709551616) by lia.
  rewrite (Z.mod_small (Int64.unsigned (Int64.add r Int64.one))
      18446744073709551616) by
    (pose proof (Int64.unsigned_range (Int64.add r Int64.one)); lia).
  change
    (@toZ BitToZ
       (if increment64_carry r then inr tt else inl tt) * 18446744073709551616 +
     Int64.unsigned (Int64.add r Int64.one) =
     Int64.unsigned r + 0 + 1).
  destruct (increment64_carry r) eqn:Hcarry.
  - apply increment64_carry_is_overflow in Hcarry.
    unfold Int64.max_unsigned in Hcarry. rewrite HM in Hcarry.
    pose proof (Int64.unsigned_range (Int64.add r Int64.one)) as HP.
    rewrite HM in HP.
    change (1 * 18446744073709551616 +
      Int64.unsigned (Int64.add r Int64.one) =
      Int64.unsigned r + 0 + 1).
    rewrite Hcarry in Hadd. destruct Hadd as [Hplus|Hwrap].
    + lia.
    + rewrite Hcarry, Hwrap. lia.
  - assert (Hnotmax : Int64.unsigned r <> 18446744073709551615).
    { intro Heq. assert (Hmax : Int64.unsigned r = Int64.max_unsigned).
      { unfold Int64.max_unsigned. rewrite HM. exact Heq. }
      apply increment64_carry_is_overflow in Hmax. congruence. }
    assert (Hsmall : Int64.unsigned r + 1 < 18446744073709551616) by lia.
    pose proof (Int64.unsigned_range (Int64.add r Int64.one)) as HP.
    rewrite HM in HP.
    change (0 * 18446744073709551616 +
      Int64.unsigned (Int64.add r Int64.one) =
      Int64.unsigned r + 0 + 1).
    destruct Hadd as [Hplus|Hwrap]; [rewrite Hplus; simpl; lia|lia].
Qed.

Lemma increment64_values_denote_input r (x : Ty.tySem (Word 6)) :
  Int64.unsigned r = @toZ (WordToZ 6) x ->
  ((if increment64_carry r then inr tt else inl tt),
    decode_wide W64 (increment64_payload r)) = increment64_spec_value x.
Proof.
  intros Hr. rewrite <- (from_toZ x), <- Hr.
  apply increment64_values_denote_spec.
Qed.

(** Symbolic arithmetic bridge for the canonical Simplicity increment_32 jet. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Arith.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec C.jet_increment_wide_word.
Local Open Scope Z_scope.

Definition increment32_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 5) (Ty.Prod Bit (Word 5)) :=
  @increment_word_spec term 5.

Definition increment32_spec_value :
    Ty.tySem (Word 5) -> Ty.tySem (Ty.Prod Bit (Word 5)) :=
  @increment32_spec Alg.CoreFunSem.

Definition increment32_carry (r : int64) : bool :=
  Int64.ltu (Int64.repr 4294967294) r.

Definition increment32_payload (r : int64) : int64 := Int64.add r Int64.one.

Lemma increment32_values_denote_spec r :
  Int64.unsigned r <= 4294967295 ->
  ((if increment32_carry r then inr tt else inl tt),
    decode_wide W32 (Int64.zero_ext 32 (increment32_payload r))) =
  increment32_spec_value (@fromZ (WordToZ 5) (Int64.unsigned r)).
Proof.
  intros Hr.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 5))).
  unfold increment32_spec_value, increment32_spec.
  rewrite increment_word_spec_fun, Word.fullAdder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 5)).
  unfold increment32_carry, increment32_payload, decode_wide.
  rewrite !to_fromZ, Word.zero_correct.
  change (@toZ BitToZ
     (if Int64.ltu (Int64.repr 4294967294) r then inr tt else inl tt)
       * 4294967296 +
     Int64.unsigned (Int64.zero_ext 32 (Int64.add r Int64.one)) mod 4294967296 =
     Int64.unsigned r mod 4294967296 + 0 + 1).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  unfold Int64.add.
  pose proof (Int64.unsigned_range r) as HU.
  rewrite Int64.unsigned_one.
  rewrite Int64.unsigned_repr by
    (change (0 <= Int64.unsigned r + 1 <= 18446744073709551615); lia).
  change (@toZ BitToZ
     (if Int64.ltu (Int64.repr 4294967294) r then inr tt else inl tt)
       * 4294967296 +
     ((Int64.unsigned r + 1) mod 4294967296) mod 4294967296 =
     Int64.unsigned r mod 4294967296 + 0 + 1).
  rewrite Z.mod_mod by lia.
  rewrite (Z.mod_small (Int64.unsigned r) 4294967296) by lia.
  unfold Int64.ltu.
  change (Int64.unsigned (Int64.repr 4294967294)) with 4294967294.
  destruct (zlt 4294967294 (Int64.unsigned r)) as [HC|HC].
  - assert (HM : Int64.unsigned r = 4294967295) by lia.
    rewrite HM. reflexivity.
  - change (0 * 4294967296 + (Int64.unsigned r + 1) mod 4294967296 =
      Int64.unsigned r + 0 + 1).
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma increment32_values_denote_input r (x : Ty.tySem (Word 5)) :
  Int64.unsigned r = @toZ (WordToZ 5) x ->
  ((if increment32_carry r then inr tt else inl tt),
    decode_wide W32 (Int64.zero_ext 32 (increment32_payload r))) =
    increment32_spec_value x.
Proof.
  intros Hr.
  pose proof (@toZ_mod (WordToZ 5) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  rewrite (bitSize_Word 5) in Hmod.
  change (@toZ (WordToZ 5) x =
    Z.modulo (@toZ (WordToZ 5) x) 4294967296) in Hmod.
  assert (Hrange : 0 <= @toZ (WordToZ 5) x <= 4294967295).
  { rewrite Hmod.
    pose proof (Z.mod_pos_bound (@toZ (WordToZ 5) x) 4294967296 ltac:(lia)).
    lia. }
  rewrite <- (from_toZ x), <- Hr.
  apply increment32_values_denote_spec. lia.
Qed.

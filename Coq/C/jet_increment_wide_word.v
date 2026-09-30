(** Symbolic arithmetic bridge for the canonical Simplicity increment program. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Monad Simplicity.Util.Arith.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec.
Require Export C.jet_toZ.
Require Export C.jet_increment_spec.
Local Open Scope Z_scope.

Lemma full_increment_word_spec_parametric n :
    Alg.Core.Parametric (fun term => @full_increment_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold full_increment_word_spec.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.take_Parametric. apply Alg.iden_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.drop_Parametric. apply Alg.iden_Parametric.
      * apply Alg.comp_Parametric.
        -- apply Alg.unit_Parametric.
        -- apply Word.zero_Parametric.
  - apply Word.fullAdder_Parametric.
Qed.

Lemma increment_word_spec_parametric n :
    Alg.Core.Parametric (fun term => @increment_word_spec term n).
Proof.
  intros alg1 alg2 R. unfold increment_word_spec.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Bit.true_Parametric.
    + apply Alg.iden_Parametric.
  - apply full_increment_word_spec_parametric.
Qed.

Lemma increment_word_spec_initial n (M : CIMonad.type) (x : Ty.tySem (Word n)) :
  @increment_word_spec (Alg.CoreSem M) n x =
    eta (@increment_word_spec Alg.CoreFunSem n x).
Proof.
  exact (@Alg.CoreSem_initial M (Word n) (Ty.Prod Bit (Word n))
    (fun (term : Alg.Core.Algebra) => @increment_word_spec term n)
    (increment_word_spec_parametric n) x).
Qed.

Lemma increment_word_spec_fun n (x : Ty.tySem (Word n)) :
  @increment_word_spec Alg.CoreFunSem n x =
    @Word.fullAdder n Alg.CoreFunSem
      (inr tt, (x, @Word.zero n Alg.CoreFunSem tt)).
Proof. reflexivity. Qed.

Definition increment16_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 4) (Ty.Prod Bit (Word 4)) :=
  @increment_word_spec term 4.

Definition increment16_spec_value :
    Ty.tySem (Word 4) -> Ty.tySem (Ty.Prod Bit (Word 4)) :=
  @increment16_spec Alg.CoreFunSem.

Definition increment16_carry (r : int64) : bool :=
  Int64.ltu (Int64.repr 65534) r.

Definition increment16_payload (r : int64) : int64 := Int64.add r Int64.one.

Lemma increment16_values_denote_spec r :
  Int64.unsigned r <= 65535 ->
  ((if increment16_carry r then inr tt else inl tt),
    decode_wide W16 (Int64.zero_ext 16 (increment16_payload r))) =
  increment16_spec_value (@fromZ (WordToZ 4) (Int64.unsigned r)).
Proof.
  intros Hr.
  pose proof (Int64.unsigned_range r) as HU.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 4))).
  unfold increment16_spec_value, increment16_spec.
  rewrite increment_word_spec_fun, Word.fullAdder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 4)).
  unfold increment16_carry, increment16_payload, decode_wide.
  rewrite !to_fromZ, Word.zero_correct.
  change (@toZ BitToZ
     (if Int64.ltu (Int64.repr 65534) r then inr tt else inl tt)
       * 65536 +
     Int64.unsigned
       (Int64.zero_ext 16 (Int64.add r Int64.one)) mod 65536 =
     Int64.unsigned r mod 65536 + 0 + 1).
  rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
  unfold Int64.add.
  rewrite Int64.unsigned_one.
  rewrite Int64.unsigned_repr by
    (change (0 <= Int64.unsigned r + 1 <= 18446744073709551615); lia).
  change (@toZ BitToZ
     (if Int64.ltu (Int64.repr 65534) r then inr tt else inl tt)
       * 65536 +
     ((Int64.unsigned r + 1) mod 65536) mod 65536 =
     Int64.unsigned r mod 65536 + 0 + 1).
  rewrite Z.mod_mod by lia.
  rewrite (Z.mod_small (Int64.unsigned r) 65536) by lia.
  unfold Int64.ltu.
  change (Int64.unsigned (Int64.repr 65534)) with 65534.
  destruct (zlt 65534 (Int64.unsigned r)) as [HC|HC].
  - assert (HM : Int64.unsigned r = 65535) by lia.
    rewrite HM. reflexivity.
  - change (0 * 65536 + (Int64.unsigned r + 1) mod 65536 =
      Int64.unsigned r + 0 + 1).
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma increment16_values_denote_input r (x : Ty.tySem (Word 4)) :
  Int64.unsigned r = @toZ (WordToZ 4) x ->
  ((if increment16_carry r then inr tt else inl tt),
    decode_wide W16 (Int64.zero_ext 16 (increment16_payload r))) =
    increment16_spec_value x.
Proof.
  intros Hr.
  pose proof (@toZ_mod (WordToZ 4) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  rewrite (bitSize_Word 4) in Hmod.
  change (@toZ (WordToZ 4) x =
    Z.modulo (@toZ (WordToZ 4) x) 65536) in Hmod.
  assert (Hrange : 0 <= @toZ (WordToZ 4) x <= 65535).
  { rewrite Hmod.
    pose proof (Z.mod_pos_bound (@toZ (WordToZ 4) x) 65536 ltac:(lia)).
    lia. }
  rewrite <- (from_toZ x), <- Hr.
  apply increment16_values_denote_spec. lia.
Qed.

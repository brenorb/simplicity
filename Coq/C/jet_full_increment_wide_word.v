(** Carry-input wide increments reuse the verified increment and representation lemmas. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_wide C.jet_wide_spec C.jet_toZ C.jet_word_repr C.jet_readBit_layout.
Require Import C.jet_increment_spec C.jet_increment_wide_word.
Require Import C.jet_increment32_wide_word C.jet_increment64_wide_word.
Require Import C.jet_full_increment8_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_full_increment_max s : Z := match s with
  | W16 => 65535 | W32 => 4294967295 | W64 => Int64.max_unsigned end.
Definition wide_full_increment_carry s cin r :=
  Int64.ltu (Int64.sub (Int64.repr (wide_full_increment_max s)) (bit_long cin)) r.
Definition wide_full_increment_payload cin r := Int64.add r (bit_long cin).

Lemma full_increment_word_spec_zero n (x : Ty.tySem (Word n)) :
  @full_increment_word_spec Alg.CoreFunSem n (inl tt, x) = (inl tt, x).
Proof.
  apply (toZ_injective (PairToZ BitToZ (WordToZ n))).
  rewrite full_increment_word_spec_numeric, (@toZ_Pair BitToZ (WordToZ n)).
  change (@toZ (WordToZ n) x + 0 = 0 * two_power_nat (bitSize (WordToZ n)) + @toZ (WordToZ n) x).
  lia.
Qed.

Lemma wide_full_increment_input_bound s (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  Int64.unsigned r <= wide_full_increment_max s.
Proof.
  intros Hr. pose proof (word_toZ_range (wide_log s) x) as Hrange.
  destruct s; rewrite Hr.
  - change (0 <= @toZ (WordToZ 4) x < 65536) in Hrange.
    change (@toZ (WordToZ 4) x <= 65535). lia.
  - change (0 <= @toZ (WordToZ 5) x < 4294967296) in Hrange.
    change (@toZ (WordToZ 5) x <= 4294967295). lia.
  - change (0 <= @toZ (WordToZ 6) x < 18446744073709551616) in Hrange.
    change (@toZ (WordToZ 6) x <= 18446744073709551615). lia.
Qed.

Lemma wide_full_increment_false_carry s r :
  Int64.unsigned r <= wide_full_increment_max s ->
  wide_full_increment_carry s Datatypes.false r = Datatypes.false.
Proof.
  intros Hr. unfold wide_full_increment_carry. change (bit_long Datatypes.false) with Int64.zero.
  rewrite Int64.sub_zero_l.
  unfold Int64.ltu.
  rewrite Int64.unsigned_repr by (destruct s; change Int64.max_unsigned with 18446744073709551615; cbn; lia).
  apply zlt_false. lia.
Qed.

Lemma wide_full_increment_values_denote_input s (c : Ty.tySem Bit)
    (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  ((if wide_full_increment_carry s (Bit.toBool c) r then inr tt else inl tt),
    decode_wide s (Int64.zero_ext (wide_bits s) (wide_full_increment_payload (Bit.toBool c) r))) =
    @full_increment_word_spec Alg.CoreFunSem (wide_log s) (c, x).
Proof.
  intros Hr. destruct c as [[]|[]].
  - rewrite full_increment_word_spec_zero.
    rewrite wide_full_increment_false_carry by (eapply wide_full_increment_input_bound; exact Hr).
    unfold wide_full_increment_payload. change (bit_long (Bit.toBool (inl tt))) with Int64.zero.
    rewrite Int64.add_zero. f_equal.
    apply (toZ_injective (WordToZ (wide_log s))).
    unfold decode_wide. rewrite to_fromZ.
    destruct s.
    + rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
      rewrite Hr. change ((@toZ (WordToZ 4) x mod 65536) mod 65536 = @toZ (WordToZ 4) x).
      rewrite Z.mod_mod by lia. apply word_toZ_mod.
    + rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
      rewrite Hr. change ((@toZ (WordToZ 5) x mod 4294967296) mod 4294967296 = @toZ (WordToZ 5) x).
      rewrite Z.mod_mod by lia. apply word_toZ_mod.
    + rewrite Int64.zero_ext_above by (change (64 >= 64); lia).
      rewrite Hr. apply word_toZ_mod.
  - destruct s.
    + change (((if increment16_carry r then inr tt else inl tt),
        decode_wide W16 (Int64.zero_ext 16 (increment16_payload r))) = increment16_spec_value x).
      apply increment16_values_denote_input; exact Hr.
    + change (((if increment32_carry r then inr tt else inl tt),
        decode_wide W32 (Int64.zero_ext 32 (increment32_payload r))) = increment32_spec_value x).
      apply increment32_values_denote_input; exact Hr.
    + change (((if increment64_carry r then inr tt else inl tt),
        decode_wide W64 (Int64.zero_ext 64 (increment64_payload r))) = increment64_spec_value x).
      rewrite Int64.zero_ext_above by (change (64 >= 64); lia).
      apply increment64_values_denote_input; exact Hr.
Qed.

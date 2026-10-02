(** Shared symbolic full-add bridge, including the wrapping 64-bit carrier. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_wide C.jet_wide_spec C.jet_toZ C.jet_readBit_layout.
Require Import C.jet_full_increment_wide_word.
Require Import C.jet_add16_wide_word C.jet_add32_wide_word C.jet_add64_wide_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_full_add_spec s {term : Alg.Core.Algebra} := @Word.fullAdder (wide_log s) term.
Definition wide_full_add_first_carry s r t :=
  Int64.ltu (Int64.sub (Int64.repr (wide_full_increment_max s)) t) r.
Definition wide_full_add_carry s cin r t :=
  orb (wide_full_add_first_carry s r t)
    (wide_full_increment_carry s cin (Int64.add r t)).
Definition wide_full_add_payload cin r t := Int64.add (Int64.add r t) (bit_long cin).

Lemma wide_full_add_first_overflow s r t :
  Int64.unsigned r <= wide_full_increment_max s ->
  Int64.unsigned t <= wide_full_increment_max s ->
  wide_full_add_first_carry s r t =
    (wide_full_increment_max s <? Int64.unsigned r + Int64.unsigned t).
Proof.
  intros HR HT. destruct s.
  - apply add16_carry_denotes_overflow; assumption.
  - apply add32_carry_denotes_overflow; assumption.
  - apply add64_carry_denotes_overflow.
Qed.
Lemma bit_long_unsigned_range cin : 0 <= Int64.unsigned (bit_long cin) <= 1.
Proof. destruct cin; [change (0 <= 1 <= 1)|change (0 <= 0 <= 1)]; lia. Qed.
Lemma wide_full_add_second_overflow s cin v :
  wide_full_increment_carry s cin v =
    (wide_full_increment_max s <? Int64.unsigned v + Int64.unsigned (bit_long cin)).
Proof.
  pose proof (bit_long_unsigned_range cin) as HC.
  assert (HM : 1 <= wide_full_increment_max s <= Int64.max_unsigned).
  { destruct s; change Int64.max_unsigned with 18446744073709551615; cbn; lia. }
  assert (HU : Int64.unsigned (Int64.repr (wide_full_increment_max s)) = wide_full_increment_max s).
  { apply Int64.unsigned_repr. lia. }
  unfold wide_full_increment_carry, Int64.ltu, Int64.sub. rewrite HU.
  rewrite Int64.unsigned_repr by lia.
  destruct (zlt (wide_full_increment_max s - Int64.unsigned (bit_long cin)) (Int64.unsigned v));
    symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma wide_full_add_overflow s cin r t :
  Int64.unsigned r <= wide_full_increment_max s ->
  Int64.unsigned t <= wide_full_increment_max s ->
  wide_full_add_carry s cin r t =
    (wide_full_increment_max s <? Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)).
Proof.
  intros HR HT. pose proof (Int64.unsigned_range r) as HR0.
  pose proof (Int64.unsigned_range t) as HT0. pose proof (bit_long_unsigned_range cin) as HC.
  pose proof (wide_full_add_first_overflow s r t HR HT) as Hfirst.
  unfold wide_full_add_carry. rewrite Hfirst.
  destruct (wide_full_increment_max s <? Int64.unsigned r + Int64.unsigned t) eqn:Hoverflow.
  - cbn. symmetry. apply Z.ltb_lt. apply Z.ltb_lt in Hoverflow. lia.
  - apply Z.ltb_ge in Hoverflow. cbn.
    rewrite wide_full_add_second_overflow.
    assert (Hsum : Int64.unsigned (Int64.add r t) = Int64.unsigned r + Int64.unsigned t).
    { unfold Int64.add. apply Int64.unsigned_repr.
      assert (HM : wide_full_increment_max s <= Int64.max_unsigned).
      { destruct s; change Int64.max_unsigned with 18446744073709551615; cbn; lia. }
      lia. }
    rewrite Hsum. reflexivity.
Qed.

Lemma wide_full_add_payload_numeric s cin r t :
  Int64.unsigned r <= wide_full_increment_max s ->
  Int64.unsigned t <= wide_full_increment_max s ->
  @toZ (WordToZ (wide_log s))
    (decode_wide s (Int64.zero_ext (wide_bits s) (wide_full_add_payload cin r t))) =
    (Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)) mod (wide_full_increment_max s + 1).
Proof.
  intros HR HT. pose proof (Int64.unsigned_range r) as HR0.
  pose proof (Int64.unsigned_range t) as HT0. pose proof (bit_long_unsigned_range cin) as HC.
  unfold decode_wide. rewrite to_fromZ.
  destruct s.
  - rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
    change (Int64.unsigned r <= 65535) in HR. change (Int64.unsigned t <= 65535) in HT.
    unfold wide_full_add_payload, Int64.add.
    rewrite (Int64.unsigned_repr (Int64.unsigned r + Int64.unsigned t)) by
      (change Int64.max_unsigned with 18446744073709551615;
       change (Int64.unsigned r <= 65535) in HR; change (Int64.unsigned t <= 65535) in HT; lia).
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    change (((Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)) mod 65536) mod 65536 =
      (Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)) mod 65536).
    apply Z.mod_mod. lia.
  - rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
    change (Int64.unsigned r <= 4294967295) in HR. change (Int64.unsigned t <= 4294967295) in HT.
    unfold wide_full_add_payload, Int64.add.
    rewrite (Int64.unsigned_repr (Int64.unsigned r + Int64.unsigned t)) by
      (change Int64.max_unsigned with 18446744073709551615;
       change (Int64.unsigned r <= 4294967295) in HR; change (Int64.unsigned t <= 4294967295) in HT; lia).
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    change (((Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)) mod 4294967296) mod 4294967296 =
      (Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)) mod 4294967296).
    apply Z.mod_mod. lia.
  - rewrite Int64.zero_ext_above by (change (64 >= 64); lia).
    unfold wide_full_add_payload, Int64.add. rewrite !Int64.unsigned_repr_eq.
    change ((((Int64.unsigned r + Int64.unsigned t) mod 18446744073709551616 +
      Int64.unsigned (bit_long cin)) mod 18446744073709551616) mod 18446744073709551616 =
      (Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long cin)) mod 18446744073709551616).
    rewrite Z.mod_mod by lia. apply Z.add_mod_idemp_l. lia.
Qed.

Lemma wide_full_add_values_denote_input s (c : Ty.tySem Bit)
    (x y : Ty.tySem (Word (wide_log s))) r t :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  Int64.unsigned t = @toZ (WordToZ (wide_log s)) y ->
  ((if wide_full_add_carry s (Bit.toBool c) r t then inr tt else inl tt),
    decode_wide s (Int64.zero_ext (wide_bits s) (wide_full_add_payload (Bit.toBool c) r t))) =
    @wide_full_add_spec s Alg.CoreFunSem (c, (x, y)).
Proof.
  intros HR HT. pose proof (wide_full_increment_input_bound s x r HR) as HRM.
  pose proof (wide_full_increment_input_bound s y t HT) as HTM.
  pose proof (Int64.unsigned_range r) as HR0. pose proof (Int64.unsigned_range t) as HT0.
  pose proof (bit_long_unsigned_range (Bit.toBool c)) as HC.
  assert (Hbit : Int64.unsigned (bit_long (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  assert (Hmodulus : two_power_nat (bitSize (WordToZ (wide_log s))) = wide_full_increment_max s + 1)
    by (destruct s; reflexivity).
  assert (HM : 0 < wide_full_increment_max s + 1) by (destruct s; cbn; lia).
  apply (toZ_injective (PairToZ BitToZ (WordToZ (wide_log s)))).
  unfold wide_full_add_spec. rewrite Word.fullAdder_correct, (@toZ_Pair BitToZ (WordToZ (wide_log s))).
  rewrite wide_full_add_payload_numeric, wide_full_add_overflow by assumption.
  rewrite Hmodulus, <- HR, <- HT, <- Hbit.
  set (total := Int64.unsigned r + Int64.unsigned t + Int64.unsigned (bit_long (Bit.toBool c))).
  set (modulus := wide_full_increment_max s + 1).
  assert (Htotal : 0 <= total < 2 * modulus) by (unfold total, modulus; lia).
  destruct (wide_full_increment_max s <? total) eqn:Hcarry.
  - apply Z.ltb_lt in Hcarry.
    change (1 * modulus + total mod modulus = total).
    replace (total mod modulus) with (total - modulus); [lia|].
    apply Z.mod_unique with (q := 1); unfold modulus in *; lia.
  - apply Z.ltb_ge in Hcarry.
    change (0 * modulus + total mod modulus = total).
    rewrite Z.mod_small by (unfold modulus in *; lia). lia.
Qed.
Lemma wide_full_add_spec_parametric s : Alg.Core.Parametric (@wide_full_add_spec s).
Proof. intros alg1 alg2 R. apply Word.fullAdder_Parametric. Qed.

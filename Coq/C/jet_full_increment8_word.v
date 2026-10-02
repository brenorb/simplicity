(** Exact carry-input increment representation, reusing the checked byte adder. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_readBit_layout C.jet_add8 C.jet_add8_word.
Require Import C.jet_increment_spec C.jet_increment_wide_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_increment8_carry cin r :=
  Int.ltu (Int.sub (Int.repr 255) (bit_int cin)) (Int.zero_ext 8 r).
Definition full_increment8_raw cin r :=
  Int.add (Int.mul Int.one (Int.zero_ext 8 r)) (bit_int cin).
Definition full_increment8_payload cin r := Int.zero_ext 8 (full_increment8_raw cin r).

Lemma full_increment_word_spec_numeric n (c : Ty.tySem Bit) (x : Ty.tySem (Word n)) :
  @toZ (PairToZ BitToZ (WordToZ n)) (@full_increment_word_spec Alg.CoreFunSem n (c, x)) =
    @toZ (WordToZ n) x + @toZ BitToZ c.
Proof.
  change (@toZ (PairToZ BitToZ (WordToZ n))
    (@Word.fullAdder n Alg.CoreFunSem (c, (x, @Word.zero n Alg.CoreFunSem tt))) =
      @toZ (WordToZ n) x + @toZ BitToZ c).
  rewrite Word.fullAdder_correct, Word.zero_correct. lia.
Qed.

Lemma bit_int_zero_ext8 cin : Int.zero_ext 8 (bit_int cin) = bit_int cin.
Proof. destruct cin; reflexivity. Qed.
Lemma bit_int_unsigned cin :
  Int.unsigned (bit_int cin) = @toZ BitToZ (if cin then inr tt else inl tt).
Proof. destruct cin; reflexivity. Qed.
Lemma full_increment8_payload_add cin r :
  full_increment8_payload cin r = add8_byte r (bit_int cin).
Proof.
  unfold full_increment8_payload, full_increment8_raw, add8_byte, add8_sum_raw, add8_u.
  rewrite bit_int_zero_ext8. reflexivity.
Qed.
Lemma full_increment8_carry_add cin r :
  full_increment8_carry cin r = Int.ltu (Int.sub (Int.repr 255) (add8_u (bit_int cin))) (add8_u r).
Proof. unfold full_increment8_carry, add8_u. rewrite bit_int_zero_ext8. reflexivity. Qed.

Lemma full_increment8_values_denote_spec (c : Ty.tySem Bit) payload :
  ((if full_increment8_carry (Bit.toBool c) (read8_result payload) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned (full_increment8_payload (Bit.toBool c) (read8_result payload))))) =
    @full_increment8_spec Alg.CoreFunSem (c, decode_word8 payload).
Proof.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 3))).
  unfold full_increment8_spec. rewrite full_increment_word_spec_numeric.
  rewrite (@toZ_Pair BitToZ (WordToZ 3)).
  rewrite full_increment8_payload_add, full_increment8_carry_add, add8_overflow.
  rewrite decode_word8_of_int, add8_byte_unsigned.
  unfold add8_u at 2 4. rewrite !bit_int_zero_ext8, !read8_result_unsigned.
  assert (Hbit : Int.unsigned (bit_int (Bit.toBool c)) = @toZ BitToZ c)
    by (destruct c as [[]|[]]; reflexivity).
  rewrite Hbit.
  set (a := @toZ (WordToZ 3) (decode_word8 payload)).
  set (b := @toZ BitToZ c).
  assert (HA : 0 <= a < 256).
  { unfold a, decode_word8. rewrite to_fromZ. apply Z.mod_pos_bound. lia. }
  assert (HB : 0 <= b <= 1) by (unfold b; destruct c as [[]|[]]; cbn; lia).
  change (@toZ BitToZ (if 255 <? a + b then inr tt else inl tt) * 256 +
    ((a + b) mod 256) mod 256 = a + b).
  rewrite Z.mod_mod by lia. destruct (255 <? a + b) eqn:Hcarry.
  - apply Z.ltb_lt in Hcarry.
    change (1 * 256 + (a + b) mod 256 = a + b).
    replace ((a + b) mod 256) with (a + b - 256); [lia|].
    apply Z.mod_unique with (q := 1); lia.
  - apply Z.ltb_ge in Hcarry.
    change (0 * 256 + (a + b) mod 256 = a + b).
    rewrite Z.mod_small by lia. lia.
Qed.

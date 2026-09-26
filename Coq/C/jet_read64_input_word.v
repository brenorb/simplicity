(** Logical bit interpretation of the actual two-word read64 extraction. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Memory.
Require Import Simplicity.Word Simplicity.Util.Arith.
Require Import C.jets C.jet_input_layout C.jet_read16_input_word.
Require Import C.jet_read32_input_word C.jet_frame_arith.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition read64_aligned_at (high : int64) : int64 := high.

Definition read64_crossing_at (cursor : Z) (high low : int64) : int64 :=
  let first := 64 - cursor mod 64 in
  let rest := cursor mod 64 in
  Int64.or
    (Int64.shl (Int64.zero_ext first high) (Int64.repr rest))
    (Int64.zero_ext rest (Int64.shru low (Int64.repr (64 - rest)))).

Lemma frame_input_word_bits64_nth (x : Ty.tySem (Word 6)) i :
  (i < 64)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ 6) x) (63 - Z.of_nat i)).
Proof.
  intros Hi. rewrite frame_input_word_bits_nth by (change (i < 64)%nat; exact Hi).
  assert (Hindex : Z.of_nat (64 - S i) = 63 - Z.of_nat i).
  { rewrite Nat2Z.inj_sub by lia. rewrite (Nat2Z.inj_succ i).
    change (64 - (Z.of_nat i + 1) = 63 - Z.of_nat i). lia. }
  cbn [Nat.pow].
  change
    (Some (Z.testbit (@toZ (WordToZ 6) x) (Z.of_nat (64 - S i))) =
     Some (Z.testbit (@toZ (WordToZ 6) x) (63 - Z.of_nat i))).
  rewrite Hindex. reflexivity.
Qed.

Lemma frame_input_word_at_bit64 m bw edge cursor
    (x : Ty.tySem (Word 6)) i :
  frame_input_word_at m bw edge cursor x -> (i < 64)%nat ->
  frame_input_bit_at m bw edge (cursor + Z.of_nat i)
    (Z.testbit (@toZ (WordToZ 6) x) (63 - Z.of_nat i)).
Proof.
  intros Hinput Hi. unfold frame_input_word_at, frame_input_bits_at in Hinput.
  eapply Hinput. apply frame_input_word_bits64_nth. exact Hi.
Qed.

Lemma word64_toZ_range (x : Ty.tySem (Word 6)) :
  0 <= @toZ (WordToZ 6) x < 18446744073709551616.
Proof.
  pose proof (@toZ_mod (WordToZ 6) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  rewrite (bitSize_Word 6) in Hmod.
  change (@toZ (WordToZ 6) x =
    Z.modulo (@toZ (WordToZ 6) x) 18446744073709551616) in Hmod.
  rewrite Hmod. apply Z.mod_pos_bound. lia.
Qed.

Lemma word64_toZ_high_bits (x : Ty.tySem (Word 6)) j :
  64 <= j -> Z.testbit (@toZ (WordToZ 6) x) j = false.
Proof.
  intros Hj. pose proof (@toZ_mod (WordToZ 6) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  rewrite (bitSize_Word 6) in Hmod.
  change (@toZ (WordToZ 6) x =
    Z.modulo (@toZ (WordToZ 6) x) 18446744073709551616) in Hmod.
  rewrite Hmod. replace 18446744073709551616 with (2 ^ 64) by reflexivity.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma read64_crossing_at_bits cursor high low j :
  0 < cursor mod 64 < 64 -> 0 <= j < 64 ->
  Int64.testbit (read64_crossing_at cursor high low) j =
    if zlt j (cursor mod 64)
    then Int64.testbit low (j + 64 - cursor mod 64)
    else Int64.testbit high (j - cursor mod 64).
Proof.
  intros Hr Hj.
  assert (Hfirst : 0 < 64 - cursor mod 64 < 64) by lia.
  assert (Hword : Int64.zwordsize = 64) by reflexivity.
  unfold read64_crossing_at.
  rewrite Int64.bits_or by exact Hj.
  rewrite Int64.bits_shl by exact Hj.
  rewrite !cursor_unsigned by lia.
  destruct (zlt j (cursor mod 64)) as [Hlow|Hhigh].
  - rewrite Bool.orb_false_l.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_shru by exact Hj. rewrite cursor_unsigned by lia.
    rewrite Hword. rewrite zlt_true by lia.
    replace (j + (64 - cursor mod 64)) with (j + 64 - cursor mod 64) by lia.
    reflexivity.
  - rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_false by lia.
    rewrite Bool.orb_false_r. reflexivity.
Qed.

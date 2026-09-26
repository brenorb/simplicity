(** Exact logical interpretation of non-crossing generated read32 results. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Memory.
Require Import Simplicity.Word Simplicity.Util.Arith.
Require Import C.jets C.jet_input_layout C.jet_read16_input_word.
Require Import C.jet_read32_layout_exec C.jet_frame_arith.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma frame_input_word_bits32_nth (x : Ty.tySem (Word 5)) i :
  (i < 32)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i)).
Proof.
  intros Hi. rewrite frame_input_word_bits_nth by exact Hi.
  assert (Hindex : Z.of_nat (32 - S i) = 31 - Z.of_nat i).
  { rewrite Nat2Z.inj_sub by lia. rewrite (Nat2Z.inj_succ i).
    change (32 - (Z.of_nat i + 1) = 31 - Z.of_nat i). lia. }
  cbn [Nat.pow].
  change
    (Some (Z.testbit (@toZ (WordToZ 5) x) (Z.of_nat (32 - S i))) =
     Some (Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i))).
  rewrite Hindex. reflexivity.
Qed.

Lemma frame_input_word_at_bit32 m bw edge cursor
    (x : Ty.tySem (Word 5)) i :
  frame_input_word_at m bw edge cursor x -> (i < 32)%nat ->
  frame_input_bit_at m bw edge (cursor + Z.of_nat i)
    (Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i)).
Proof.
  intros Hinput Hi. unfold frame_input_word_at, frame_input_bits_at in Hinput.
  eapply Hinput. apply frame_input_word_bits32_nth. exact Hi.
Qed.

Lemma word32_toZ_range (x : Ty.tySem (Word 5)) :
  0 <= @toZ (WordToZ 5) x < 4294967296.
Proof.
  pose proof (@toZ_mod (WordToZ 5) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  rewrite (bitSize_Word 5) in Hmod.
  change (@toZ (WordToZ 5) x =
    Z.modulo (@toZ (WordToZ 5) x) 4294967296) in Hmod.
  rewrite Hmod. apply Z.mod_pos_bound. lia.
Qed.

Lemma word32_toZ_high_bits (x : Ty.tySem (Word 5)) j :
  32 <= j -> Z.testbit (@toZ (WordToZ 5) x) j = false.
Proof.
  intros Hj.
  pose proof (@toZ_mod (WordToZ 5) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  rewrite (bitSize_Word 5) in Hmod.
  change (@toZ (WordToZ 5) x =
    Z.modulo (@toZ (WordToZ 5) x) 4294967296) in Hmod.
  rewrite Hmod. replace 4294967296 with (2 ^ 32) by reflexivity.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma read32_input_bit_non_crossing m bw edge cursor
    (x : Ty.tySem (Word 5)) high i :
  0 <= cursor -> cursor mod 64 <= 32 -> (i < 32)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Z.testbit (Int64.unsigned high) (63 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i).
Proof.
  intros HC Hr Hi Hinput Hhigh.
  pose proof (frame_input_word_at_bit32 m bw edge cursor x i Hinput Hi) as Hbit.
  destruct Hbit as [_ [_ [w [Hw Hvalue]]]].
  destruct (cursor_add_index_non_crossing cursor (Z.of_nat i)
      HC ltac:(lia) ltac:(pose proof (Nat2Z.is_nonneg i); lia)) as [Hq Hmod].
  rewrite Hq in Hw. rewrite Hhigh in Hw. inversion Hw; subst w.
  rewrite Hmod in Hvalue.
  replace (63 - (cursor mod 64 + Z.of_nat i)) with
      (63 - cursor mod 64 - Z.of_nat i) in Hvalue by lia.
  symmetry. exact Hvalue.
Qed.

Lemma read32_non_crossing_at_input_bit m bw edge cursor high
    (x : Ty.tySem (Word 5)) i :
  0 <= cursor -> cursor mod 64 <= 32 -> (i < 32)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Int64.testbit (read32_non_crossing_at cursor high) (31 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i).
Proof.
  intros HC Hr Hi Hinput Hhigh.
  assert (HM : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (HiZ : 0 <= Z.of_nat i < 32).
  { split; [apply Nat2Z.is_nonneg |]. exact (proj1 (Nat2Z.inj_lt i 32) Hi). }
  unfold read32_non_crossing_at.
  rewrite Int64.bits_zero_ext by lia.
  rewrite zlt_true by lia.
  rewrite Int64.bits_shru by
    (change (0 <= 31 - Z.of_nat i < 64); lia).
  rewrite cursor_unsigned by lia.
  rewrite zlt_true by
    (change (31 - Z.of_nat i + (32 - cursor mod 64) < 64); lia).
  replace (31 - Z.of_nat i + (32 - cursor mod 64)) with
      (63 - cursor mod 64 - Z.of_nat i) by lia.
  exact (read32_input_bit_non_crossing m bw edge cursor x high i
    HC Hr Hi Hinput Hhigh).
Qed.

Lemma read32_non_crossing_at_repr m bw edge cursor high
    (x : Ty.tySem (Word 5)) :
  0 <= cursor -> cursor mod 64 <= 32 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  read32_non_crossing_at cursor high =
    Int64.repr (@toZ (WordToZ 5) x).
Proof.
  intros HC Hr Hinput Hhigh. apply Int64.same_bits_eq. intros j Hj.
  destruct (Z_lt_ge_dec j 32) as [Hlow|Hhighbit].
  - set (i := Z.to_nat (31 - j)).
    assert (Hi : (i < 32)%nat).
    { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    pose proof (read32_non_crossing_at_input_bit m bw edge cursor high x i
      HC Hr Hi Hinput Hhigh) as HB.
    replace (31 - Z.of_nat i) with j in HB by
      (unfold i; rewrite Z2Nat.id by lia; lia).
    rewrite HB. rewrite Int64.testbit_repr by exact Hj. reflexivity.
  - unfold read32_non_crossing_at.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_false by lia.
    rewrite Int64.testbit_repr by exact Hj.
    symmetry. apply word32_toZ_high_bits. lia.
Qed.

Lemma read32_non_crossing_at_unsigned m bw edge cursor high
    (x : Ty.tySem (Word 5)) :
  0 <= cursor -> cursor mod 64 <= 32 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Int64.unsigned (read32_non_crossing_at cursor high) =
    @toZ (WordToZ 5) x.
Proof.
  intros HC Hr Hinput Hhigh.
  rewrite (read32_non_crossing_at_repr m bw edge cursor high x
    HC Hr Hinput Hhigh).
  apply Int64.unsigned_repr.
  pose proof (word32_toZ_range x).
  change (0 <= @toZ (WordToZ 5) x <= 18446744073709551615).
  lia.
Qed.

Lemma read32_crossing_at_bits cursor high low j :
  32 < cursor mod 64 < 64 -> 0 <= j < 64 ->
  Int64.testbit (read32_crossing_at cursor high low) j =
    if zlt j (cursor mod 64 - 32)
    then Int64.testbit low (j + 64 - (cursor mod 64 - 32))
    else if zlt j 32
      then Int64.testbit high (j - (cursor mod 64 - 32))
      else false.
Proof.
  intros Hcross Hj.
  assert (Hr : cursor mod 64 < 64) by lia.
  assert (Hrest : 0 < cursor mod 64 - 32 < 32) by lia.
  assert (Hfirst : 0 < 64 - cursor mod 64 < 32) by lia.
  assert (Hsum : (64 - cursor mod 64) + (cursor mod 64 - 32) = 32) by lia.
  unfold read32_crossing_at.
  rewrite Int64.bits_or by exact Hj.
  rewrite Int64.bits_shl by exact Hj.
  rewrite !cursor_unsigned by lia.
  destruct (zlt j (cursor mod 64 - 32)) as [Hlow|Hnotlow].
  - rewrite Bool.orb_false_l.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_shru by exact Hj. rewrite cursor_unsigned by lia.
    rewrite zlt_true by
      (change (j + (64 - (cursor mod 64 - 32)) < 64); lia).
    f_equal. lia.
  - rewrite !Int64.bits_zero_ext by lia.
    destruct (zlt j 32) as [Hwithin|Habove].
    + rewrite zlt_true by lia. rewrite zlt_false by lia.
      apply Bool.orb_false_r.
    + rewrite !zlt_false by lia. reflexivity.
Qed.

Lemma read32_input_bit_crossing_high m bw edge cursor
    (x : Ty.tySem (Word 5)) high i :
  0 <= cursor -> 32 < cursor mod 64 < 64 -> (i < 32)%nat ->
  Z.of_nat i < 64 - cursor mod 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Z.testbit (Int64.unsigned high) (63 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hbefore Hinput Hhigh.
  pose proof (frame_input_word_at_bit32 m bw edge cursor x i Hinput Hi) as Hbit.
  destruct Hbit as [_ [_ [w [Hw Hvalue]]]].
  destruct (cursor_add_index_non_crossing cursor (Z.of_nat i)
      HC ltac:(lia) ltac:(lia)) as [Hq Hmod].
  replace (edge - 8 * (1 + (cursor + Z.of_nat i) / 64)) with
      (edge - 8 * (1 + cursor / 64)) in Hw by (rewrite Hq; reflexivity).
  rewrite Hhigh in Hw. inversion Hw; subst w.
  rewrite Hmod in Hvalue.
  replace (63 - (cursor mod 64 + Z.of_nat i)) with
      (63 - cursor mod 64 - Z.of_nat i) in Hvalue by lia.
  symmetry. exact Hvalue.
Qed.

Lemma read32_input_bit_crossing_low m bw edge cursor
    (x : Ty.tySem (Word 5)) low i :
  0 <= cursor -> 32 < cursor mod 64 < 64 -> (i < 32)%nat ->
  64 - cursor mod 64 <= Z.of_nat i ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Z.testbit (Int64.unsigned low) (127 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hafter Hinput Hlow.
  pose proof (frame_input_word_at_bit32 m bw edge cursor x i Hinput Hi) as Hbit.
  destruct Hbit as [_ [_ [w [Hw Hvalue]]]].
  destruct (cursor_add_index_crossing cursor (Z.of_nat i)
      HC ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq Hmod].
  replace (edge - 8 * (1 + (cursor + Z.of_nat i) / 64)) with
      (edge - 8 * (2 + cursor / 64)) in Hw by (rewrite Hq; lia).
  rewrite Hlow in Hw. inversion Hw; subst w.
  rewrite Hmod in Hvalue.
  replace (63 - (cursor mod 64 + Z.of_nat i - 64)) with
      (127 - cursor mod 64 - Z.of_nat i) in Hvalue by lia.
  symmetry. exact Hvalue.
Qed.

Lemma read32_crossing_at_input_bit m bw edge cursor high low
    (x : Ty.tySem (Word 5)) i :
  0 <= cursor -> 32 < cursor mod 64 < 64 -> (i < 32)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Int64.testbit (read32_crossing_at cursor high low) (31 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 5) x) (31 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hinput Hhigh Hlow.
  pose proof (read32_crossing_at_bits cursor high low (31 - Z.of_nat i)
    Hcross ltac:(pose proof (Nat2Z.is_nonneg i);
      pose proof (Nat2Z.inj_lt i 32); lia)) as Hbits.
  rewrite Hbits.
  destruct (zlt (31 - Z.of_nat i) (cursor mod 64 - 32)) as [Hto_low|Hto_high].
  - pose proof (read32_input_bit_crossing_low m bw edge cursor x low i
      HC Hcross Hi ltac:(lia) Hinput Hlow) as Hsource.
    replace (31 - Z.of_nat i + 64 - (cursor mod 64 - 32)) with
        (127 - cursor mod 64 - Z.of_nat i) by lia.
    exact Hsource.
  - rewrite zlt_true by lia.
    pose proof (read32_input_bit_crossing_high m bw edge cursor x high i
      HC Hcross Hi ltac:(lia) Hinput Hhigh) as Hsource.
    replace (31 - Z.of_nat i - (cursor mod 64 - 32)) with
        (63 - cursor mod 64 - Z.of_nat i) by lia.
    exact Hsource.
Qed.

Lemma read32_crossing_at_repr m bw edge cursor high low
    (x : Ty.tySem (Word 5)) :
  0 <= cursor -> 32 < cursor mod 64 < 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  read32_crossing_at cursor high low = Int64.repr (@toZ (WordToZ 5) x).
Proof.
  intros HC Hcross Hinput Hhigh Hlow.
  apply Int64.same_bits_eq. intros j Hj.
  change (0 <= j < 64) in Hj.
  destruct (Z_lt_ge_dec j 32) as [Hwithin|Habove].
  - set (i := Z.to_nat (31 - j)).
    assert (Hi : (i < 32)%nat).
    { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    pose proof (read32_crossing_at_input_bit m bw edge cursor high low x i
      HC Hcross Hi Hinput Hhigh Hlow) as HB.
    replace (31 - Z.of_nat i) with j in HB by
      (unfold i; rewrite Z2Nat.id by lia; lia).
    rewrite HB. rewrite Int64.testbit_repr by exact Hj. reflexivity.
  - rewrite read32_crossing_at_bits by assumption.
    rewrite zlt_false by lia. rewrite zlt_false by lia.
    rewrite Int64.testbit_repr by exact Hj.
    symmetry. apply word32_toZ_high_bits. lia.
Qed.

Lemma read32_crossing_at_unsigned m bw edge cursor high low
    (x : Ty.tySem (Word 5)) :
  0 <= cursor -> 32 < cursor mod 64 < 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Int64.unsigned (read32_crossing_at cursor high low) =
    @toZ (WordToZ 5) x.
Proof.
  intros HC Hcross Hinput Hhigh Hlow.
  rewrite (read32_crossing_at_repr m bw edge cursor high low x
    HC Hcross Hinput Hhigh Hlow).
  apply Int64.unsigned_repr.
  pose proof (word32_toZ_range x).
  change (0 <= @toZ (WordToZ 5) x <= 18446744073709551615).
  lia.
Qed.

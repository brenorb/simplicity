(** Logical Word16 input bits and exact interpretation of the generated reader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Util.Arith.
Require Import C.jets C.jet_exec C.jet_input_layout.
Require Import C.jet_frame_layout.
Require Import C.jet_read16_layout_total C.jet_read16_layout_exec.
Require Import C.jet_frame_arith.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma nth_error_seq_lt start n i :
  (i < n)%nat -> nth_error (seq start n) i = Some (start + i)%nat.
Proof.
  revert start i. induction n; intros start i Hi; [lia|].
  destruct i; simpl.
  - f_equal; lia.
  - rewrite IHn by lia. f_equal; lia.
Qed.

Lemma frame_input_word_bits_nth {n} (x : Ty.tySem (Word n)) i :
  (i < Nat.pow 2 n)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ n) x)
      (Z.of_nat (Nat.pow 2 n - S i))).
Proof.
  intros Hi. unfold frame_input_word_bits. rewrite nth_error_map.
  rewrite nth_error_seq_lt by exact Hi. simpl. reflexivity.
Qed.

Lemma frame_input_word_bits16_nth (x : Ty.tySem (Word 4)) i :
  (i < 16)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i)).
Proof.
  intros Hi. rewrite frame_input_word_bits_nth by exact Hi.
  assert (Hindex :
    Z.of_nat (16 - S i) = 15 - Z.of_nat i).
  { rewrite Nat2Z.inj_sub by lia. rewrite (Nat2Z.inj_succ i).
    change (16 - (Z.of_nat i + 1) = 15 - Z.of_nat i). lia. }
  cbn [Nat.pow].
  change
    (Some (Z.testbit (@toZ (WordToZ 4) x) (Z.of_nat (16 - S i))) =
     Some (Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i))).
  rewrite Hindex. reflexivity.
Qed.

Lemma frame_input_word_at_bit16 m bw edge cursor (x : Ty.tySem (Word 4)) i :
  frame_input_word_at m bw edge cursor x -> (i < 16)%nat ->
  frame_input_bit_at m bw edge (cursor + Z.of_nat i)
    (Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i)).
Proof.
  intros Hinput Hi. unfold frame_input_word_at, frame_input_bits_at in Hinput.
  eapply Hinput. apply frame_input_word_bits16_nth. exact Hi.
Qed.

Lemma cursor_add_index_non_crossing cursor i :
  0 <= cursor -> 0 <= i -> cursor mod 64 + i < 64 ->
  (cursor + i) / 64 = cursor / 64 /\
  (cursor + i) mod 64 = cursor mod 64 + i.
Proof.
  intros HC HI Hr.
  assert (Hrem : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hdecomp : cursor + i = 64 * (cursor / 64) + (cursor mod 64 + i)).
  { pose proof (Z.div_mod cursor 64 ltac:(lia)). lia. }
  split.
  - symmetry. apply (Z.div_unique (cursor + i) 64 (cursor / 64)
      (cursor mod 64 + i)); [left; lia | exact Hdecomp].
  - symmetry. apply (Z.mod_unique (cursor + i) 64 (cursor / 64)
      (cursor mod 64 + i)); [left; lia | exact Hdecomp].
Qed.

Lemma cursor_add_index_crossing cursor i :
  0 <= cursor -> 0 <= i -> 64 <= cursor mod 64 + i -> cursor mod 64 + i < 128 ->
  (cursor + i) / 64 = cursor / 64 + 1 /\
  (cursor + i) mod 64 = cursor mod 64 + i - 64.
Proof.
  intros HC HI Hr Hupper.
  assert (Hrem : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hdecomp : cursor + i = 64 * (cursor / 64 + 1) +
      (cursor mod 64 + i - 64)).
  { pose proof (Z.div_mod cursor 64 ltac:(lia)). lia. }
  split.
  - symmetry. apply (Z.div_unique (cursor + i) 64 (cursor / 64 + 1)
      (cursor mod 64 + i - 64)); [left; lia | exact Hdecomp].
  - symmetry. apply (Z.mod_unique (cursor + i) 64 (cursor / 64 + 1)
      (cursor mod 64 + i - 64)); [left; lia | exact Hdecomp].
Qed.

Lemma word16_toZ_range (x : Ty.tySem (Word 4)) :
  0 <= @toZ (WordToZ 4) x < 65536.
Proof.
  pose proof (@toZ_mod (WordToZ 4) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  pose proof (bitSize_Word 4) as Hsize.
  rewrite Hsize in Hmod.
  change (@toZ (WordToZ 4) x =
    Z.modulo (@toZ (WordToZ 4) x) 65536) in Hmod.
  rewrite Hmod. apply Z.mod_pos_bound. lia.
Qed.

Lemma word16_toZ_high_bits (x : Ty.tySem (Word 4)) j :
  16 <= j -> Z.testbit (@toZ (WordToZ 4) x) j = false.
Proof.
  intros Hj.
  pose proof (@toZ_mod (WordToZ 4) x) as Hmod.
  rewrite two_power_nat_equiv in Hmod.
  pose proof (bitSize_Word 4) as Hsize.
  rewrite Hsize in Hmod.
  change (@toZ (WordToZ 4) x =
    Z.modulo (@toZ (WordToZ 4) x) 65536) in Hmod.
  rewrite Hmod. replace 65536 with (2 ^ 16) by reflexivity.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma read16_input_bit_non_crossing m bw edge cursor
    (x : Ty.tySem (Word 4)) high i :
  0 <= cursor -> cursor mod 64 <= 48 -> (i < 16)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Z.testbit (Int64.unsigned high) (63 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i).
Proof.
  intros HC Hr Hi Hinput Hhigh.
  pose proof (frame_input_word_at_bit16 m bw edge cursor x i Hinput Hi) as Hbit.
  destruct Hbit as [_ [_ [w [Hw Hvalue]]]].
  destruct (cursor_add_index_non_crossing cursor (Z.of_nat i)
      HC ltac:(lia) ltac:(pose proof (Nat2Z.is_nonneg i); lia)) as [Hq Hmod].
  rewrite Hq in Hw. rewrite Hhigh in Hw. inversion Hw; subst w.
  rewrite Hmod in Hvalue.
  replace (63 - (cursor mod 64 + Z.of_nat i)) with
      (63 - cursor mod 64 - Z.of_nat i) in Hvalue by lia.
  symmetry. exact Hvalue.
Qed.

Lemma read16_non_crossing_at_input_bit m bw edge cursor high
    (x : Ty.tySem (Word 4)) i :
  0 <= cursor -> cursor mod 64 <= 48 -> (i < 16)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Int64.testbit (read16_non_crossing_at cursor high) (15 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i).
Proof.
  intros HC Hr Hi Hinput Hhigh.
  assert (HM : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (HiZ : 0 <= Z.of_nat i < 16).
  { split; [apply Nat2Z.is_nonneg |].
    exact (proj1 (Nat2Z.inj_lt i 16) Hi). }
  unfold read16_non_crossing_at.
  rewrite Int64.bits_zero_ext by lia.
  rewrite zlt_true by lia.
  rewrite Int64.bits_shru by (change (0 <= 15 - Z.of_nat i < 64); lia).
  rewrite cursor_unsigned by lia.
  rewrite zlt_true by
    (change (15 - Z.of_nat i + (48 - cursor mod 64) < 64); lia).
  replace (15 - Z.of_nat i + (48 - cursor mod 64)) with
      (63 - cursor mod 64 - Z.of_nat i) by lia.
  exact (read16_input_bit_non_crossing m bw edge cursor x high i
    HC Hr Hi Hinput Hhigh).
Qed.

Lemma read16_non_crossing_at_repr m bw edge cursor high (x : Ty.tySem (Word 4)) :
  0 <= cursor -> cursor mod 64 <= 48 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  read16_non_crossing_at cursor high =
    Int64.repr (@toZ (WordToZ 4) x).
Proof.
  intros HC Hr Hinput Hhigh. apply Int64.same_bits_eq. intros j Hj.
  destruct (Z_lt_ge_dec j 16) as [Hlow | Hhighbit].
  - set (i := Z.to_nat (15 - j)).
    assert (Hi : (i < 16)%nat).
    { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    pose proof (read16_non_crossing_at_input_bit m bw edge cursor high x i
      HC Hr Hi Hinput Hhigh) as HB.
    replace (15 - Z.of_nat i) with j in HB by
      (unfold i; rewrite Z2Nat.id by lia; lia).
    rewrite HB. rewrite Int64.testbit_repr by exact Hj. reflexivity.
  - unfold read16_non_crossing_at.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_false by lia.
    rewrite Int64.testbit_repr by exact Hj.
    symmetry. apply word16_toZ_high_bits. lia.
Qed.

Lemma read16_non_crossing_at_unsigned m bw edge cursor high (x : Ty.tySem (Word 4)) :
  0 <= cursor -> cursor mod 64 <= 48 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Int64.unsigned (read16_non_crossing_at cursor high) =
    @toZ (WordToZ 4) x.
Proof.
  intros HC Hr Hinput Hhigh.
  rewrite (read16_non_crossing_at_repr m bw edge cursor high x
    HC Hr Hinput Hhigh).
  apply Int64.unsigned_repr.
  pose proof (word16_toZ_range x).
  change (0 <= @toZ (WordToZ 4) x <= 18446744073709551615).
  lia.
Qed.

Lemma read16_crossing_at_bits cursor high low j :
  48 < cursor mod 64 < 64 -> 0 <= j < 64 ->
  Int64.testbit (read16_crossing_at cursor high low) j =
    if zlt j (cursor mod 64 - 48)
    then Int64.testbit low (j + 64 - (cursor mod 64 - 48))
    else if zlt j 16
      then Int64.testbit high (j - (cursor mod 64 - 48))
      else false.
Proof.
  intros Hcross Hj.
  assert (Hr : cursor mod 64 < 64) by lia.
  assert (Ht : 0 < cursor mod 64 - 48 < 16) by lia.
  assert (Hk : 0 < 64 - cursor mod 64 < 16) by lia.
  assert (Hsum : (64 - cursor mod 64) + (cursor mod 64 - 48) = 16) by lia.
  unfold read16_crossing_at.
  rewrite Int64.bits_or by exact Hj.
  rewrite Int64.bits_shl by exact Hj.
  rewrite !cursor_unsigned by lia.
  destruct (zlt j (cursor mod 64 - 48)) as [Hlow|Hnotlow].
  - rewrite Bool.orb_false_l.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_shru by exact Hj. rewrite cursor_unsigned by lia.
    rewrite zlt_true by
      (change (j + (64 - (cursor mod 64 - 48)) < 64); lia).
    f_equal. lia.
  - rewrite !Int64.bits_zero_ext by lia.
    destruct (zlt j 16) as [Hwithin|Habove].
    + rewrite zlt_true by lia.
      rewrite zlt_false by lia. apply Bool.orb_false_r.
    + rewrite !zlt_false by lia.
      reflexivity.
Qed.

Lemma read16_input_bit_crossing_high m bw edge cursor
    (x : Ty.tySem (Word 4)) high i :
  0 <= cursor -> 48 < cursor mod 64 < 64 -> (i < 16)%nat ->
  Z.of_nat i < 64 - cursor mod 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Z.testbit (Int64.unsigned high) (63 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hbefore Hinput Hhigh.
  pose proof (frame_input_word_at_bit16 m bw edge cursor x i Hinput Hi) as Hbit.
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

Lemma read16_input_bit_crossing_low m bw edge cursor
    (x : Ty.tySem (Word 4)) low i :
  0 <= cursor -> 48 < cursor mod 64 < 64 -> (i < 16)%nat ->
  64 - cursor mod 64 <= Z.of_nat i ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Z.testbit (Int64.unsigned low) (127 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hafter Hinput Hlow.
  pose proof (frame_input_word_at_bit16 m bw edge cursor x i Hinput Hi) as Hbit.
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

Lemma read16_crossing_at_input_bit m bw edge cursor high low
    (x : Ty.tySem (Word 4)) i :
  0 <= cursor -> 48 < cursor mod 64 < 64 -> (i < 16)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Int64.testbit (read16_crossing_at cursor high low) (15 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hinput Hhigh Hlow.
  pose proof (read16_crossing_at_bits cursor high low (15 - Z.of_nat i)
    Hcross ltac:(pose proof (Nat2Z.is_nonneg i); pose proof (Nat2Z.inj_lt i 16); lia)) as Hbits.
  rewrite Hbits.
  destruct (zlt (15 - Z.of_nat i) (cursor mod 64 - 48)) as [Hto_low|Hto_high].
  -
    pose proof (read16_input_bit_crossing_low m bw edge cursor x low i
      HC Hcross Hi ltac:(lia) Hinput Hlow) as Hsource.
    replace (15 - Z.of_nat i + 64 - (cursor mod 64 - 48)) with
        (127 - cursor mod 64 - Z.of_nat i) by lia.
    exact Hsource.
  - rewrite zlt_true by lia.
    pose proof (read16_input_bit_crossing_high m bw edge cursor x high i
      HC Hcross Hi ltac:(lia) Hinput Hhigh) as Hsource.
    replace (15 - Z.of_nat i - (cursor mod 64 - 48)) with
        (63 - cursor mod 64 - Z.of_nat i) by lia.
    exact Hsource.
Qed.

Lemma read16_crossing_at_repr m bw edge cursor high low
    (x : Ty.tySem (Word 4)) :
  0 <= cursor -> 48 < cursor mod 64 < 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  read16_crossing_at cursor high low = Int64.repr (@toZ (WordToZ 4) x).
Proof.
  intros HC Hcross Hinput Hhigh Hlow.
  apply Int64.same_bits_eq. intros j Hj.
  change (0 <= j < 64) in Hj.
  destruct (Z_lt_ge_dec j 16) as [Hwithin|Habove].
  - set (i := Z.to_nat (15 - j)).
    assert (Hi : (i < 16)%nat).
    { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    pose proof (read16_crossing_at_input_bit m bw edge cursor high low x i
      HC Hcross Hi Hinput Hhigh Hlow) as HB.
    replace (15 - Z.of_nat i) with j in HB by
      (unfold i; rewrite Z2Nat.id by lia; lia).
    rewrite HB. rewrite Int64.testbit_repr by exact Hj. reflexivity.
  - rewrite read16_crossing_at_bits by assumption.
    rewrite zlt_false by lia. rewrite zlt_false by lia.
    rewrite Int64.testbit_repr by exact Hj.
    symmetry. apply word16_toZ_high_bits. lia.
Qed.

Lemma read16_crossing_at_unsigned m bw edge cursor high low
    (x : Ty.tySem (Word 4)) :
  0 <= cursor -> 48 < cursor mod 64 < 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Int64.unsigned (read16_crossing_at cursor high low) =
    @toZ (WordToZ 4) x.
Proof.
  intros HC Hcross Hinput Hhigh Hlow.
  rewrite (read16_crossing_at_repr m bw edge cursor high low x
    HC Hcross Hinput Hhigh Hlow).
  apply Int64.unsigned_repr.
  pose proof (word16_toZ_range x).
  change (0 <= @toZ (WordToZ 4) x <= 18446744073709551615).
  lia.
Qed.

Lemma read16_layout_value_unsigned m bw edge cursor high low
    (x : Ty.tySem (Word 4)) :
  0 <= cursor ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (48 < cursor mod 64 ->
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Int64.unsigned (read16_layout_value cursor high low) =
    @toZ (WordToZ 4) x.
Proof.
  intros HC Hinput Hhigh Hlow.
  unfold read16_layout_value.
  destruct (Z_le_dec (cursor mod 64) 48) as [Hnoncross|Hcross].
  - exact (read16_non_crossing_at_unsigned m bw edge cursor high x
      HC Hnoncross Hinput Hhigh).
  - assert (Hcrossing : 48 < cursor mod 64 < 64).
    { pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)). lia. }
    exact (read16_crossing_at_unsigned m bw edge cursor high low x
      HC Hcrossing Hinput Hhigh (Hlow ltac:(lia))).
Qed.

Lemma read16_input_loads m bw edge cursor (x : Ty.tySem (Word 4)) :
  0 <= cursor <= Int64.max_unsigned - 16 ->
  frame_input_word_at m bw edge cursor x ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned /\
  exists high low,
    Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) =
      Some (Vlong high) /\
    (48 < cursor mod 64 ->
      8 * (2 + cursor / 64) <= edge /\
      Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) =
        Some (Vlong low)).
Proof.
  intros HC Hinput.
  pose proof (frame_input_word_at_bit16
    m bw edge cursor x 0 Hinput ltac:(lia)) as Hfirst.
  replace (cursor + Z.of_nat 0) with cursor in Hfirst by lia.
  destruct Hfirst as [_ [HE [high [HH _]]]].
  split; [exact HE|].
  destruct (Z_lt_dec 48 (cursor mod 64)) as [HX|HN].
  - set (k := 64 - cursor mod 64).
    assert (HK : 1 <= k <= 15) by
      (unfold k;
       pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
    assert (Hnat : Z.of_nat (Z.to_nat k) = k)
      by (apply Z2Nat.id; lia).
    assert (Hi : (Z.to_nat k < 16)%nat).
    { apply Nat2Z.inj_lt. rewrite Hnat. lia. }
    pose proof (frame_input_word_at_bit16
      m bw edge cursor x (Z.to_nat k) Hinput Hi) as Hnext.
    unfold frame_input_bit_at in Hnext.
    rewrite Hnat in Hnext.
    destruct Hnext as [_ [HElow [low [HL _]]]].
    destruct (cursor_add_index_crossing cursor k
      ltac:(lia) ltac:(lia)
      ltac:(unfold k; lia) ltac:(unfold k; lia)) as [HQ HR].
    rewrite HQ in HElow, HL.
    replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64)
      in HElow, HL by lia.
    exists high, low.
    split; [exact HH|].
    intros _. split; [exact (proj1 HElow)|exact HL].
  - exists high, Int64.zero.
    split; [exact HH|].
    intros HX. lia.
Qed.

Theorem eval_read16_word_at m bf base bw edge cursor (x : Ty.tySem (Word 4)) :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 16 ->
  frame_fields_at m bf base bw edge cursor ->
  frame_input_word_at m bw edge cursor x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf r,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read16)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ 4) x /\
    frame_fields_at mf bf base bw edge (cursor + 16) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/
      base + 16 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HF Hinput PW Hsep.
  destruct (read16_input_loads m bw edge cursor x HC Hinput)
    as [HE [high [low [Hhigh Hlow]]]].
  destruct (eval_read16_layout_total m bf base bw edge cursor high low
      HB HC HE HF Hhigh Hlow PW Hsep)
    as [mf [Heval [Hfields [Hloads [Hperm Hblocks]]]]].
  exists mf, (read16_layout_value cursor high low).
  split; [exact Heval|].
  split.
  - exact (read16_layout_value_unsigned m bw edge cursor high low x
      ltac:(lia) Hinput Hhigh (fun Hcross => proj2 (Hlow Hcross))).
  - split; [exact Hfields|].
    split; [exact Hloads|].
    split; [exact Hperm|exact Hblocks].
Qed.

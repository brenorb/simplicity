(** Connect the read64 extraction to its initial-memory input-word contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes ClightBigstep Memory Events.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_input_layout.
Require Import C.jet_read16_input_word C.jet_read64_input_word.
Require Import C.jet_read64_layout_total C.jet_frame_arith.
Require Import C.jet_frame_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma read64_input_bit_crossing_high m bw edge cursor
    (x : Ty.tySem (Word 6)) high i :
  0 <= cursor -> 0 < cursor mod 64 < 64 -> (i < 64)%nat ->
  Z.of_nat i < 64 - cursor mod 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Z.testbit (Int64.unsigned high) (63 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 6) x) (63 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hbefore Hinput Hhigh.
  pose proof (frame_input_word_at_bit64 m bw edge cursor x i Hinput Hi) as Hbit.
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

Lemma read64_input_bit_crossing_low m bw edge cursor
    (x : Ty.tySem (Word 6)) low i :
  0 <= cursor -> 0 < cursor mod 64 < 64 -> (i < 64)%nat ->
  64 - cursor mod 64 <= Z.of_nat i ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Z.testbit (Int64.unsigned low) (127 - cursor mod 64 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 6) x) (63 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hafter Hinput Hlow.
  pose proof (frame_input_word_at_bit64 m bw edge cursor x i Hinput Hi) as Hbit.
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

Lemma read64_crossing_at_input_bit m bw edge cursor high low
    (x : Ty.tySem (Word 6)) i :
  0 <= cursor -> 0 < cursor mod 64 < 64 -> (i < 64)%nat ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Int64.testbit (read64_crossing_at cursor high low) (63 - Z.of_nat i) =
    Z.testbit (@toZ (WordToZ 6) x) (63 - Z.of_nat i).
Proof.
  intros HC Hcross Hi Hinput Hhigh Hlow.
  pose proof (read64_crossing_at_bits cursor high low (63 - Z.of_nat i)
    Hcross ltac:(pose proof (Nat2Z.is_nonneg i);
      pose proof (Nat2Z.inj_lt i 64); lia)) as Hbits.
  rewrite Hbits.
  destruct (zlt (63 - Z.of_nat i) (cursor mod 64)) as [Hlowbit|Hhighbit].
  - pose proof (read64_input_bit_crossing_low m bw edge cursor x low i
      HC Hcross Hi ltac:(lia) Hinput Hlow) as Hsource.
    replace (63 - Z.of_nat i + 64 - cursor mod 64)
      with (127 - cursor mod 64 - Z.of_nat i) by lia.
    exact Hsource.
  -
    pose proof (read64_input_bit_crossing_high m bw edge cursor x high i
      HC Hcross Hi ltac:(lia) Hinput Hhigh) as Hsource.
    replace (63 - Z.of_nat i - cursor mod 64)
      with (63 - cursor mod 64 - Z.of_nat i) by lia.
    exact Hsource.
Qed.

Lemma read64_crossing_at_repr m bw edge cursor high low
    (x : Ty.tySem (Word 6)) :
  0 <= cursor -> 0 < cursor mod 64 < 64 ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  read64_crossing_at cursor high low = Int64.repr (@toZ (WordToZ 6) x).
Proof.
  intros HC Hcross Hinput Hhigh Hlow.
  apply Int64.same_bits_eq. intros j Hj.
  change (0 <= j < 64) in Hj.
  set (i := Z.to_nat (63 - j)).
  assert (Hi : (i < 64)%nat).
  { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  pose proof (read64_crossing_at_input_bit m bw edge cursor high low x i
    HC Hcross Hi Hinput Hhigh Hlow) as HB.
  replace (63 - Z.of_nat i) with j in HB by
    (unfold i; rewrite Z2Nat.id by lia; lia).
  rewrite HB. rewrite Int64.testbit_repr by exact Hj. reflexivity.
Qed.

Lemma read64_layout_value_unsigned m bw edge cursor high low
    (x : Ty.tySem (Word 6)) :
  0 <= cursor -> frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (cursor mod 64 <> 0 ->
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Int64.unsigned (read64_layout_value cursor high low) =
    @toZ (WordToZ 6) x.
Proof.
  intros HC Hinput Hhigh Hlow.
  assert (Hmax : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  unfold read64_layout_value.
  destruct (Z.eq_dec (cursor mod 64) 0) as [HA|HX].
  - subst.
    assert (Hrepr : high = Int64.repr (@toZ (WordToZ 6) x)).
    { apply Int64.same_bits_eq. intros j Hj.
      change (0 <= j < 64) in Hj.
      set (i := Z.to_nat (63 - j)).
      assert (Hi : (i < 64)%nat).
      { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
      pose proof (frame_input_word_at_bit64 m bw edge cursor x i Hinput Hi) as Hbit.
      destruct Hbit as [_ [_ [w [Hw Hvalue]]]].
      destruct (cursor_add_index_non_crossing cursor (Z.of_nat i)
          HC ltac:(lia) ltac:(pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia))
        as [Hq Hmod].
      replace (edge - 8 * (1 + (cursor + Z.of_nat i) / 64)) with
          (edge - 8 * (1 + cursor / 64)) in Hw by (rewrite Hq; reflexivity).
      rewrite Hhigh in Hw. inversion Hw; subst w. rewrite Hmod in Hvalue.
      replace (63 - (cursor mod 64 + Z.of_nat i)) with j in Hvalue by
        (unfold i; rewrite Z2Nat.id by lia; rewrite HA; lia).
      replace (63 - Z.of_nat i) with j in Hvalue by
        (unfold i; rewrite Z2Nat.id by lia; lia).
      change (Z.testbit (Int64.unsigned high) j =
        Z.testbit (Int64.unsigned (Int64.repr (@toZ (WordToZ 6) x))) j).
      rewrite Int64.unsigned_repr by (pose proof (word64_toZ_range x); rewrite Hmax; lia).
      symmetry; exact Hvalue. }
    unfold read64_aligned_at. rewrite Hrepr, Int64.unsigned_repr.
    2:{ pose proof (word64_toZ_range x); rewrite Hmax; lia. }
    reflexivity.
  - assert (Hcross : 0 < cursor mod 64 < 64).
    { pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)). lia. }
    rewrite read64_crossing_at_repr with (m := m) (bw := bw) (edge := edge)
      (cursor := cursor) (high := high) (low := low) (x := x); try assumption.
    apply Int64.unsigned_repr. pose proof (word64_toZ_range x); lia.
    exact (Hlow HX).
Qed.

Lemma read64_input_loads m bw edge cursor (x : Ty.tySem (Word 6)) :
  0 <= cursor <= Int64.max_unsigned - 64 ->
  frame_input_word_at m bw edge cursor x ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned /\
  exists high low,
    Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) /\
    (cursor mod 64 <> 0 ->
      8 * (2 + cursor / 64) <= edge /\
      Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)).
Proof.
  intros HC Hinput.
  pose proof (frame_input_word_at_bit64 m bw edge cursor x 0 Hinput ltac:(lia)) as Hbit.
  replace (cursor + Z.of_nat 0) with cursor in Hbit by lia.
  destruct Hbit as [_ [HE [high [HH _]]]].
  split; [exact HE|].
  destruct (Z.eq_dec (cursor mod 64) 0) as [HA|HX].
  - exists high, Int64.zero. split; [exact HH|]. intros Hbad. contradiction.
  - set (k := 64 - cursor mod 64).
    assert (HK : 1 <= k <= 63) by
      (unfold k; pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
    assert (Hnat : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
    assert (Hi : (Z.to_nat k < 64)%nat).
    { apply Nat2Z.inj_lt. rewrite Hnat. lia. }
    pose proof (frame_input_word_at_bit64 m bw edge cursor x (Z.to_nat k)
      Hinput Hi) as Hnext.
    unfold frame_input_bit_at in Hnext.
    rewrite Hnat in Hnext.
    destruct (cursor_add_index_crossing cursor k
      ltac:(lia) ltac:(unfold k; lia) ltac:(unfold k; lia) ltac:(unfold k; lia))
      as [HQ HR].
    destruct Hnext as [_ [HElow [low [HL _]]]].
    rewrite HQ in HElow, HL.
    replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64)
      in HElow, HL by lia.
    exists high, low. split; [exact HH|].
    intros _. split; [exact (proj1 HElow)|exact HL].
Qed.

Theorem eval_read64_word_at m bf base bw edge cursor
    (x : Ty.tySem (Word 6)) :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 64 ->
  frame_fields_at m bf base bw edge cursor ->
  frame_input_word_at m bw edge cursor x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf r,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read64)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ 6) x /\
    frame_fields_at mf bf base bw edge (cursor + 64) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/
      base + 16 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HF Hinput PW Hsep.
  destruct (read64_input_loads m bw edge cursor x HC Hinput)
    as [HE [high [low [Hhigh Hlow]]]].
  destruct (eval_read64_layout_total m bf base bw edge cursor high low
      HB HC HE HF Hhigh Hlow PW Hsep)
    as [mf [Heval [Hfields [Hloads [Hperm Hblocks]]]]].
  exists mf, (read64_layout_value cursor high low).
  split; [exact Heval|].
  split.
  - exact (read64_layout_value_unsigned m bw edge cursor high low x
      ltac:(lia) Hinput Hhigh (fun Hcross => proj2 (Hlow Hcross))).
  - split; [exact Hfields|].
    split; [exact Hloads|].
    split; [exact Hperm|exact Hblocks].
Qed.

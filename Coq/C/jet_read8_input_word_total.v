(** Symbolic byte reader interpretation from logical input bits. No padding or
    unrelated physical bits are fixed, including at word-boundary crossings. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes ClightBigstep Memory Events.
Require Import Simplicity.Word C.jet_word_repr C.jet_input_layout.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_read8 C.jet_read8_layout_total.
Require Import C.jet_read8_crossing_word C.jet_read16_input_word C.jet_frame_arith.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma frame_input_word_at_bit8 m bw edge cursor (x : Ty.tySem (Word 3)) i :
  frame_input_word_at m bw edge cursor x -> (i < 8)%nat ->
  frame_input_bit_at m bw edge (cursor + Z.of_nat i)
    (Z.testbit (@toZ (WordToZ 3) x) (7 - Z.of_nat i)).
Proof.
  intros HI Hi. apply HI. rewrite frame_input_word_bits_nth by exact Hi.
  change (Some (Z.testbit (@toZ (WordToZ 3) x) (Z.of_nat (8 - S i))) =
    Some (Z.testbit (@toZ (WordToZ 3) x) (7 - Z.of_nat i))).
  rewrite Nat2Z.inj_sub by lia. rewrite (Nat2Z.inj_succ i). f_equal; f_equal; lia.
Qed.

Lemma read8_input_loads m bw edge cursor (x : Ty.tySem (Word 3)) :
  0 <= cursor <= Int64.max_unsigned - 8 -> frame_input_word_at m bw edge cursor x ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned /\
  exists high low,
    Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) /\
    (56 < cursor mod 64 -> 8 * (2 + cursor / 64) <= edge /\
      Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)).
Proof.
  intros HC HI. pose proof (frame_input_word_at_bit8 m bw edge cursor x 0 HI ltac:(lia)) as Hfirst.
  replace (cursor + Z.of_nat 0) with cursor in Hfirst by lia.
  destruct Hfirst as [_ [HE [high [HH _]]]]. split; [exact HE|].
  destruct (Z_lt_dec 56 (cursor mod 64)) as [HX|HN].
  - set (k := 64 - cursor mod 64).
    assert (HK : 1 <= k <= 7) by (unfold k; pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
    assert (Hnat : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
    assert (Hi : (Z.to_nat k < 8)%nat) by (apply Nat2Z.inj_lt; rewrite Hnat; lia).
    pose proof (frame_input_word_at_bit8 m bw edge cursor x (Z.to_nat k) HI Hi) as Hnext.
    unfold frame_input_bit_at in Hnext. rewrite Hnat in Hnext.
    destruct Hnext as [_ [HElow [low [HL _]]]].
    destruct (cursor_add_index_crossing cursor k ltac:(lia) ltac:(lia)
      ltac:(unfold k; lia) ltac:(unfold k; lia)) as [HQ HR].
    rewrite HQ in HElow, HL.
    replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64) in HElow, HL by lia.
    exists high, low. split; [exact HH|]. intros _. split; [exact (proj1 HElow)|exact HL].
  - exists high, Int64.zero. split; [exact HH|]. intros Hbad; lia.
Qed.

Lemma read8_input_result_repr m bw edge cursor high low (x : Ty.tySem (Word 3)) :
  0 <= cursor -> frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (56 < cursor mod 64 ->
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  read8_result (read8_layout_byte cursor high low) = Int.repr (@toZ (WordToZ 3) x).
Proof.
  intros HC HI HH HL. apply Int.same_bits_eq. intros j Hj.
  change (0 <= j < 32) in Hj.
  rewrite read8_result_bits, Int.testbit_repr by exact Hj.
  destruct (zlt j 8) as [Hwithin|Habove].
  - set (i := Z.to_nat (7 - j)).
    assert (Hi : (i < 8)%nat) by (unfold i; apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
    assert (HiZ : Z.of_nat i = 7 - j) by (unfold i; rewrite Z2Nat.id by lia; reflexivity).
    pose proof (frame_input_word_at_bit8 m bw edge cursor x i HI Hi) as Hbit.
    destruct Hbit as [_ [_ [w [HW HV]]]]. rewrite HiZ in HW, HV.
    replace (7 - (7 - j)) with j in HV by lia.
    pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hr.
    unfold read8_layout_byte. destruct (Z_le_dec (cursor mod 64) 56) as [HN|HX].
    + rewrite Int64.bits_shru by (change (0 <= j < 64); lia).
      rewrite cursor_unsigned by lia. rewrite zlt_true by (change (j + (56 - cursor mod 64) < 64); lia).
      destruct (cursor_add_index_non_crossing cursor (7 - j) HC ltac:(lia) ltac:(lia)) as [HQ HM].
      rewrite HQ in HW. rewrite HH in HW. injection HW as <-.
      rewrite HM in HV. change (Z.testbit (Int64.unsigned high) (j + (56 - cursor mod 64)) =
        Z.testbit (@toZ (WordToZ 3) x) j).
      rewrite HV. f_equal; lia.
    + rewrite crossing_byte_bits by lia.
      destruct (zlt j (8 - (64 - cursor mod 64))) as [Hlow|Hhigh].
      * destruct (cursor_add_index_crossing cursor (7 - j) HC ltac:(lia) ltac:(lia) ltac:(lia)) as [HQ HM].
        rewrite HQ in HW.
        replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64) in HW by lia.
        rewrite HL in HW by lia. injection HW as <-. rewrite HM in HV.
        change (Z.testbit (Int64.unsigned low) (j + (56 + (64 - cursor mod 64))) =
          Z.testbit (@toZ (WordToZ 3) x) j).
        rewrite HV. f_equal; lia.
      * destruct (cursor_add_index_non_crossing cursor (7 - j) HC ltac:(lia) ltac:(lia)) as [HQ HM].
        rewrite HQ in HW. rewrite HH in HW. injection HW as <-. rewrite HM in HV.
        change (Z.testbit (Int64.unsigned high) (j - (8 - (64 - cursor mod 64))) =
          Z.testbit (@toZ (WordToZ 3) x) j).
        rewrite HV. f_equal; lia.
  - symmetry. apply word_toZ_high_bits. change (Z.of_nat (Nat.pow 2 3)) with 8; lia.
Qed.

Theorem eval_read8_word_at m bf base bw edge cursor (x : Ty.tySem (Word 3)) :
  frame_base_valid base -> 0 <= cursor <= Int64.max_unsigned - 8 ->
  frame_fields_at m bf base bw edge cursor -> frame_input_word_at m bw edge cursor x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (Int.repr (@toZ (WordToZ 3) x))) /\
    frame_fields_at mf bf base bw edge (cursor + 8) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HF HI HW HD.
  destruct (read8_input_loads m bw edge cursor x HC HI) as [HE [high [low [HH HL]]]].
  destruct (eval_read8_layout m bf base bw edge cursor high low HB HC HE HF HH HL HW HD)
    as [mf [HR Hrest]]. exists mf. split; [|exact Hrest].
  rewrite <- (read8_input_result_repr m bw edge cursor high low x ltac:(lia) HI HH
    (fun HX => proj2 (HL HX))). exact HR.
Qed.

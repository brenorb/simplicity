(** Exact carrier interpretation of read4 from four canonical input cells. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Ctypes ClightBigstep Events.
Require Import Simplicity.Word C.jet_word_repr.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_read4_layout C.jet_read4_crossing_layout C.jet_read4_layout_total C.jet_read4_word.
Require Import C.jet_read16_input_word C.jet_frame_arith.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma frame_input_word_at_bit4 m bw edge cursor (x : Ty.tySem (Word 2)) j :
  0 <= j < 4 -> frame_input_word_at m bw edge cursor x ->
  frame_input_bit_at m bw edge (cursor + (3 - j)) (Z.testbit (@toZ (WordToZ 2) x) j).
Proof.
  intros Hj Hin. set (i := Z.to_nat (3 - j)).
  assert (Hi : (i < 4)%nat).
  { apply Nat2Z.inj_lt. unfold i. rewrite Z2Nat.id by lia. lia. }
  assert (Hindex : Z.of_nat i = 3 - j) by (unfold i; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hnth : nth_error (frame_input_word_bits x) i = Some (Z.testbit (@toZ (WordToZ 2) x) j)).
  { rewrite frame_input_word_bits_nth by exact Hi. f_equal. f_equal.
    change (Z.of_nat (4 - S i) = j). rewrite Nat2Z.inj_sub by lia.
    rewrite (Nat2Z.inj_succ i), Hindex. lia. }
  pose proof (Hin i _ Hnth) as H. rewrite Hindex in H. exact H.
Qed.

Lemma read4_layout_input_bits m bw edge cursor high low (x : Ty.tySem (Word 2)) j :
  0 <= cursor -> frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (60 < cursor mod 64 -> Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  0 <= j < 4 ->
  Int.testbit (read4_layout_result cursor high low) j = Z.testbit (@toZ (WordToZ 2) x) j.
Proof.
  intros HC Hin HH HL Hj.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as HM.
  destruct (frame_input_word_at_bit4 m bw edge cursor x j Hj Hin)
    as [_ [_ [w [Hw Hbit]]]].
  unfold read4_layout_result. destruct (Z_le_dec (cursor mod 64) 60) as [HN|HX].
  - unfold read4_at. rewrite read4_result_bits by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_shru by (change Int64.zwordsize with 64; lia).
    rewrite cursor_unsigned by lia. rewrite zlt_true by (change (j + (60 - cursor mod 64) < 64); lia).
    destruct (cursor_add_index_non_crossing cursor (3 - j) HC ltac:(lia) ltac:(lia)) as [Hq Hmod].
    rewrite Hq, HH in Hw. inversion Hw; subst w. rewrite Hmod in Hbit.
    unfold Int64.testbit.
    replace (j + (60 - cursor mod 64)) with (63 - (cursor mod 64 + (3 - j))) by lia.
    symmetry; exact Hbit.
  - rewrite read4_crossing_result_bits by lia. rewrite zlt_true by lia.
    destruct (zlt j (4 - (64 - cursor mod 64))) as [Hlow|Hhigh].
    + destruct (cursor_add_index_crossing cursor (3 - j) HC ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq Hmod].
      rewrite Hq in Hw. replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64) in Hw by lia.
      rewrite (HL ltac:(lia)) in Hw. inversion Hw; subst w. rewrite Hmod in Hbit.
      unfold Int64.testbit.
      replace (j + (60 + (64 - cursor mod 64)))
        with (63 - (cursor mod 64 + (3 - j) - 64)) by lia.
      symmetry; exact Hbit.
    + destruct (cursor_add_index_non_crossing cursor (3 - j) HC ltac:(lia) ltac:(lia)) as [Hq Hmod].
      rewrite Hq, HH in Hw. inversion Hw; subst w. rewrite Hmod in Hbit.
      unfold Int64.testbit.
      replace (j - (4 - (64 - cursor mod 64))) with (63 - (cursor mod 64 + (3 - j))) by lia.
      symmetry; exact Hbit.
Qed.

Lemma read4_layout_input_repr m bw edge cursor high low (x : Ty.tySem (Word 2)) :
  0 <= cursor -> frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (60 < cursor mod 64 -> Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  read4_layout_result cursor high low = Int.repr (@toZ (WordToZ 2) x).
Proof.
  intros HC Hin HH HL. apply Int.same_bits_eq. intros j Hj.
  change (0 <= j < 32) in Hj. rewrite Int.testbit_repr by exact Hj.
  destruct (Z_lt_ge_dec j 4) as [Hlow|Hhigh].
  - exact (read4_layout_input_bits m bw edge cursor high low x j HC Hin HH HL ltac:(lia)).
  - assert (HX : Z.testbit (@toZ (WordToZ 2) x) j = false) by
      (apply word_toZ_high_bits; change (4 <= j); lia).
    rewrite HX. unfold read4_layout_result. destruct (Z_le_dec (cursor mod 64) 60).
    + unfold read4_at. rewrite read4_result_bits by exact Hj. rewrite zlt_false by lia. reflexivity.
    + rewrite read4_crossing_result_bits by (try exact Hj; pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
      rewrite zlt_false by lia. reflexivity.
Qed.

(** No reader execution, output value or intermediate cursor-store premise
    remains: all are derived from the initial frame and its four input cells. *)
Theorem eval_read4_word_at m bf base bw edge cursor (x : Ty.tySem (Word 2)) :
  frame_base_valid base -> 0 <= cursor <= Int64.max_unsigned - 4 ->
  frame_fields_at m bf base bw edge cursor -> frame_input_word_at m bw edge cursor x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf r,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read4)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vint r) /\
    Int.unsigned r = @toZ (WordToZ 2) x /\
    frame_fields_at mf bf base bw edge (cursor + 4) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HF Hin PW HD.
  pose proof (frame_input_word_at_bit4 m bw edge cursor x 3 ltac:(lia) Hin) as Hfirst.
  replace (cursor + (3 - 3)) with cursor in Hfirst by lia.
  destruct Hfirst as [_ [HE [high [HH Hbit]]]].
  assert (HLow : exists low, 60 < cursor mod 64 ->
    8 * (2 + cursor / 64) <= edge /\
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)).
  { destruct (Z_le_dec (cursor mod 64) 60) as [HN|HX].
    - exists Int64.zero. intros; lia.
    - pose proof (frame_input_word_at_bit4 m bw edge cursor x 0 ltac:(lia) Hin) as Hlast.
      replace (cursor + (3 - 0)) with (cursor + 3) in Hlast by lia.
      destruct Hlast as [_ [HElast [low [HL Hlast]]]].
      pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as HM.
      destruct (cursor_add_index_crossing cursor 3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq _].
      rewrite Hq in HL, HElast.
      replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64) in HL, HElast by lia.
      exists low; intros; split; [lia|exact HL]. }
  destruct HLow as [low HLow].
  destruct (eval_read4_layout m bf base bw edge cursor high low HB HC HE HF HH HLow PW HD)
    as (mf & Hcall & Hfields & Hmemory & Hperm & Hvalid).
  exists mf, (read4_layout_result cursor high low).
  split; [exact Hcall|]. split.
  - rewrite (read4_layout_input_repr m bw edge cursor high low x ltac:(lia) Hin HH
      ltac:(intros HX; exact (proj2 (HLow HX)))).
    apply Int.unsigned_repr. pose proof (word_toZ_range 2 x) as HX.
    change (0 <= @toZ (WordToZ 2) x < 16) in HX.
    change Int.max_unsigned with 4294967295; lia.
  - exact (conj Hfields (conj Hmemory (conj Hperm Hvalid))).
Qed.

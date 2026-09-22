(** Width-parametric bit algebra for the generated unsigned-long writers.
    These are the actual LSBclear/LSBkeep/shift formulas, including crossings. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_word_bits C.jet_frame_arith C.jet_frame_spec.
Local Open Scope Z_scope.

Definition put_slice n shift old x :=
  Int64.or (clear_low shift old)
    (Int64.shl (Int64.zero_ext n x) (Int64.repr (shift - n))).
Definition slice_high n k old x :=
  Int64.or (clear_low k old)
    (Int64.zero_ext k (Int64.shru x (Int64.repr (n - k)))).
Definition slice_low n k x :=
  Int64.shl (Int64.zero_ext (n - k) x) (Int64.repr (64 - (n - k))).
Definition crossing_slice n k high low :=
  Int64.or (Int64.shl (Int64.zero_ext k high) (Int64.repr (n - k)))
    (Int64.shru low (Int64.repr (64 - (n - k)))).

Lemma put_slice_bits n shift old x i :
  1 <= n <= shift -> shift <= 64 -> 0 <= i < 64 ->
  Int64.testbit (put_slice n shift old x) i =
    if zlt i shift then if zlt i (shift - n) then false
      else Int64.testbit x (i - (shift - n)) else Int64.testbit old i.
Proof.
  intros HN HS HI. unfold put_slice.
  rewrite Int64.bits_or by exact HI. rewrite clear_low_bits by lia.
  rewrite Int64.bits_shl by exact HI.
  rewrite cursor_unsigned by lia.
  destruct (zlt i (shift - n)) as [HL|HG].
  - rewrite zlt_true by lia. reflexivity.
  - rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i shift) as [HL|HG'];
      [rewrite zlt_true by lia; reflexivity|rewrite zlt_false by lia; apply orb_false_r].
Qed.

Lemma put_slice_projection n shift old x :
  1 <= n <= shift -> shift <= 64 ->
  Int64.zero_ext n (Int64.shru (put_slice n shift old x) (Int64.repr (shift - n))) =
    Int64.zero_ext n x.
Proof.
  intros HN HS. apply Int64.same_bits_eq. intros i HI. change (0 <= i < 64) in HI.
  rewrite !Int64.bits_zero_ext by lia.
  destruct (zlt i n) as [HL|HG]; [|reflexivity].
  rewrite Int64.bits_shru by exact HI. rewrite cursor_unsigned by lia.
  rewrite zlt_true by (change (i + (shift - n) < 64); lia).
  rewrite put_slice_bits by lia.
  rewrite zlt_true by lia. rewrite zlt_false by lia. f_equal; lia.
Qed.

Lemma put_slice_prefix n shift old x :
  1 <= n <= shift -> shift <= 64 -> word_outside_eq 0 shift (put_slice n shift old x) old.
Proof.
  intros HN HS i HI [HL|HG]; [lia|].
  rewrite put_slice_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Lemma slice_high_bits n k old x i :
  1 <= k < n -> n <= 64 -> 0 <= i < 64 ->
  Int64.testbit (slice_high n k old x) i =
    if zlt i k then Int64.testbit x (i + (n - k)) else Int64.testbit old i.
Proof.
  intros HK HN HI. unfold slice_high.
  rewrite Int64.bits_or by exact HI. rewrite clear_low_bits, Int64.bits_zero_ext by lia.
  destruct (zlt i k) as [HL|HG]; [cbn [orb]|apply orb_false_r].
  rewrite Int64.bits_shru by exact HI. rewrite cursor_unsigned by lia.
  rewrite zlt_true by (change (i + (n - k) < 64); lia). reflexivity.
Qed.

Lemma slice_low_bits n k x i :
  1 <= k < n -> n <= 64 -> 0 <= i < 64 ->
  Int64.testbit (slice_low n k x) i =
    if zlt i (64 - (n - k)) then false else Int64.testbit x (i - (64 - (n - k))).
Proof.
  intros HK HN HI. unfold slice_low.
  rewrite Int64.bits_shl by exact HI. rewrite cursor_unsigned by lia.
  destruct (zlt i (64 - (n - k))) as [HL|HG]; [reflexivity|].
  rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma crossing_slice_projection n k old x :
  1 <= k < n -> n <= 64 ->
  crossing_slice n k (slice_high n k old x) (slice_low n k x) = Int64.zero_ext n x.
Proof.
  intros HK HN. apply Int64.same_bits_eq. intros i HI. change (0 <= i < 64) in HI.
  unfold crossing_slice. rewrite Int64.bits_or, Int64.bits_shl, Int64.bits_shru by exact HI.
  rewrite !cursor_unsigned by lia. rewrite (Int64.bits_zero_ext n) by lia.
  destruct (zlt i (n - k)) as [HL|HG].
  - rewrite zlt_true by (change (i + (64 - (n - k)) < 64); lia).
    rewrite slice_low_bits by lia. rewrite zlt_false by lia. rewrite zlt_true by lia.
    replace (i + (64 - (n - k)) - (64 - (n - k))) with i by lia. reflexivity.
  - rewrite zlt_false by (change (i + (64 - (n - k)) >= 64); lia). rewrite orb_false_r.
    rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i n) as [HLN|HGN].
    + rewrite zlt_true by lia. rewrite slice_high_bits by lia. rewrite zlt_true by lia.
      replace (i - (n - k) + (n - k)) with i by lia. reflexivity.
    + rewrite zlt_false by lia. reflexivity.
Qed.

Lemma slice_high_prefix n k old x :
  1 <= k < n -> n <= 64 -> word_outside_eq 0 k (slice_high n k old x) old.
Proof.
  intros HK HN i HI HO. rewrite slice_high_bits by assumption.
  rewrite zlt_false by lia. reflexivity.
Qed.

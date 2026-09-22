(** Symbolic agreement of the C crossing-read casts/shifts with the bit slice. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_read8 C.jet_read8_crossing C.jet_crossing_word C.jet_crossing_byte.
Require Import C.jet_frame_arith.
Local Open Scope Z_scope.

Lemma read8_narrow_bits w i : 0 <= i < 32 ->
  Int.testbit (read8_narrow w) i =
    if zlt i 8 then Int64.testbit w i else false.
Proof.
  intros HI. unfold read8_narrow.
  rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8); [|reflexivity].
  rewrite Int.testbit_repr by exact HI. reflexivity.
Qed.

Lemma read8_result_bits w i : 0 <= i < 32 ->
  Int.testbit (read8_result w) i =
    if zlt i 8 then Int64.testbit w i else false.
Proof.
  intros HI. unfold read8_result.
  rewrite Int.or_commut, Int.or_zero, Int.zero_ext_idem by lia.
  change (Int.testbit (read8_narrow (Int64.and w (Int64.repr 255))) i =
    if zlt i 8 then Int64.testbit w i else false).
  rewrite read8_narrow_bits by exact HI.
  destruct (zlt i 8) as [HL | HG]; [|reflexivity].
  assert (HM : Int64.and w (Int64.repr 255) = Int64.zero_ext 8 w).
  { symmetry. exact (Int64.zero_ext_and 8 w ltac:(lia)). }
  rewrite HM.
  rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma crossing_byte_bits k high low i : 1 <= k <= 7 -> 0 <= i < 8 ->
  Int64.testbit (crossing_byte k high low) i =
    if zlt i (8 - k) then Int64.testbit low (i + (56 + k))
    else Int64.testbit high (i - (8 - k)).
Proof.
  intros HK HI. unfold crossing_byte.
  rewrite Int64.bits_or, Int64.bits_shl, Int64.bits_shru by (change (0 <= i < 64); lia).
  rewrite !cursor_unsigned by lia.
  destruct (zlt i (8 - k)) as [HL | HG].
  - rewrite zlt_true by (change (i + (56 + k) < 64); lia). reflexivity.
  - rewrite zlt_false by (change (i + (56 + k) >= 64); lia).
    rewrite orb_false_r. rewrite Int64.bits_zero_ext by lia.
    rewrite zlt_true by lia. reflexivity.
Qed.

Lemma read8_crossing_result_bits k high low i : 1 <= k <= 7 -> 0 <= i < 32 ->
  Int.testbit (read8_crossing_result k high low) i =
    if zlt i 8 then
      if zlt i (8 - k) then Int64.testbit low (i + (56 + k))
      else Int64.testbit high (i - (8 - k))
    else false.
Proof.
  intros HK HI. unfold read8_crossing_result.
  rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8) as [HL8 | HG8]; [|reflexivity].
  rewrite Int.bits_or by exact HI.
  unfold read8_crossing_high.
  rewrite Int.bits_zero_ext by lia. rewrite zlt_true by lia.
  rewrite Int.or_commut, Int.or_zero.
  rewrite Int.bits_zero_ext by lia. rewrite zlt_true by lia.
  rewrite Int.bits_shl by exact HI.
  rewrite crossing_shift_unsigned by exact HK.
  rewrite (read8_narrow_bits (Int64.zero_ext (8 - k) _) i) by exact HI.
  destruct (zlt i 8); [|lia].
  rewrite Int64.bits_zero_ext by lia.
  destruct (zlt i (8 - k)) as [HL | HG].
  - rewrite Int64.bits_shru by (change (0 <= i < 64); lia).
    rewrite cursor_unsigned by lia.
    rewrite zlt_true by (change (i + (56 + k) < 64); lia). reflexivity.
  - rewrite orb_false_r. rewrite read8_narrow_bits by lia.
    rewrite zlt_true by lia.
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma read8_crossing_denotes_slice k high low :
  1 <= k <= 7 ->
  read8_crossing_result k high low = read8_result (crossing_byte k high low).
Proof.
  intros HK. apply Int.same_bits_eq. intros i HI.
  change (0 <= i < 32) in HI.
  rewrite read8_crossing_result_bits, read8_result_bits by assumption.
  destruct (zlt i 8); [symmetry; apply crossing_byte_bits; lia | reflexivity].
Qed.

(** Exact bits of the nibble reader's promoted casts and crossing shifts.
    The payload stays symbolic; only the three possible crossing counts
    are computed in the carrier-count lemma. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_read4_layout C.jet_read4_crossing_layout C.jet_read4_layout_total.
Require Import C.jet_read8_crossing_word C.jet_frame_arith.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma read4_narrow_bits w i : 0 <= i < 32 ->
  Int.testbit (read4_narrow w) i = if zlt i 8 then Int64.testbit w i else false.
Proof. apply read8_narrow_bits. Qed.

Lemma read4_result_bits w i : 0 <= i < 32 ->
  Int.testbit (read4_result w) i = if zlt i 4 then Int64.testbit w i else false.
Proof.
  intros HI. unfold read4_result.
  rewrite Int.or_commut, Int.or_zero, Int.zero_ext_idem by lia.
  change (Int.testbit (read4_narrow (Int64.and w (Int64.repr 15))) i =
    if zlt i 4 then Int64.testbit w i else false).
  rewrite read4_narrow_bits by exact HI.
  assert (HM : Int64.and w (Int64.repr 15) = Int64.zero_ext 4 w).
  { symmetry. exact (Int64.zero_ext_and 4 w ltac:(lia)). }
  destruct (zlt i 8) as [HL|HG].
  - rewrite HM, Int64.bits_zero_ext by lia. reflexivity.
  - rewrite zlt_false by lia. reflexivity.
Qed.

Lemma read4_crossing_shift_unsigned k : 1 <= k <= 3 ->
  Int.unsigned (Int64.loword (Int64.repr (4 - k))) = 4 - k.
Proof.
  intros HK. assert (HC : k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct HC as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma read4_crossing_result_bits k high low i : 1 <= k <= 3 -> 0 <= i < 32 ->
  Int.testbit (read4_crossing_result k high low) i =
    if zlt i 4 then
      if zlt i (4 - k) then Int64.testbit low (i + (60 + k))
      else Int64.testbit high (i - (4 - k))
    else false.
Proof.
  intros HK HI. unfold read4_crossing_result.
  rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8) as [HL8|HG8]; [|rewrite zlt_false by lia; reflexivity].
  rewrite Int.bits_or by exact HI. unfold read4_crossing_high.
  rewrite Int.bits_zero_ext by lia. rewrite zlt_true by lia.
  rewrite Int.or_commut, Int.or_zero.
  rewrite Int.bits_zero_ext by lia. rewrite zlt_true by lia.
  rewrite Int.bits_shl by exact HI. rewrite read4_crossing_shift_unsigned by exact HK.
  rewrite (read4_narrow_bits (Int64.zero_ext (4 - k) _) i) by exact HI.
  rewrite (zlt_true _ i 8) by lia. rewrite Int64.bits_zero_ext by lia.
  destruct (zlt i (4 - k)) as [HL|HG].
  - rewrite zlt_true by lia. rewrite Int64.bits_shru by (change (0 <= i < 64); lia).
    rewrite cursor_unsigned by lia. rewrite zlt_true by (change (i + (60 + k) < 64); lia).
    reflexivity.
  - rewrite orb_false_r, read4_narrow_bits by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i 4) as [HL4|HG4].
    + rewrite zlt_true by lia. reflexivity.
    + rewrite zlt_false by lia. reflexivity.
Qed.

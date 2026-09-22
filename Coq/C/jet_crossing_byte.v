(** Symbolic interpretation of the arbitrary-byte two-word write path. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_frame_arith C.jet_frame_spec C.jet_word_bits C.jet_spec.
Require Import C.jet_word_decode C.jet_crossing_word C.jet_write8_crossing_general.
Local Open Scope Z_scope.

Lemma crossing_shift_unsigned k :
  1 <= k <= 7 ->
  Int.unsigned (Int64.loword (Int64.repr (8 - k))) = 8 - k.
Proof.
  intros HK. unfold Int64.loword.
  rewrite Int64.unsigned_repr by (change (0 <= 8 - k <= 18446744073709551615); lia).
  apply Int.unsigned_repr. change (0 <= 8 - k <= 4294967295); lia.
Qed.

Lemma crossing_high_bits k old x i :
  1 <= k <= 7 -> 0 <= i < 64 ->
  Int64.testbit (crossing_high k old x) i =
    if zlt i k then Int.testbit x (i + (8 - k)) else Int64.testbit old i.
Proof.
  intros HK HI. unfold crossing_high.
  rewrite Int64.bits_or by exact HI.
  rewrite clear_low_bits by lia. rewrite Int64.bits_zero_ext by lia.
  destruct (zlt i k) as [HL | HG]; [|apply orb_false_r].
  cbn [orb].
  rewrite Int64.testbit_repr by exact HI.
  rewrite Int.bits_signed by lia.
  rewrite zlt_true by (change (i < 32); lia).
  rewrite Int.bits_shr by (change (0 <= i < 32); lia).
  rewrite crossing_shift_unsigned by exact HK.
  rewrite zlt_true by (change (i + (8 - k) < 32); lia). reflexivity.
Qed.

Lemma crossing_low_bits k x i :
  1 <= k <= 7 -> 0 <= i < 64 ->
  Int64.testbit (crossing_low k x) i =
    if zlt i (56 + k) then false else Int.testbit x (i - (56 + k)).
Proof.
  intros HK HI. unfold crossing_low.
  rewrite Int64.bits_shl by exact HI. rewrite cursor_unsigned by lia.
  destruct (zlt i (56 + k)) as [HL | HG]; [reflexivity|].
  rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
  rewrite Int64.testbit_repr by (change (0 <= i - (56 + k) < 64); lia).
  reflexivity.
Qed.

Lemma crossing_byte_projection k old x :
  1 <= k <= 7 ->
  crossing_byte k (crossing_high k old x) (crossing_low k x) =
    Int64.zero_ext 8 (Int64.repr (Int.unsigned x)).
Proof.
  intros HK. apply Int64.same_bits_eq. intros i HI.
  change (0 <= i < 64) in HI.
  unfold crossing_byte.
  rewrite Int64.bits_or by exact HI.
  rewrite Int64.bits_shl, Int64.bits_shru by exact HI.
  rewrite !cursor_unsigned by lia.
  rewrite (Int64.bits_zero_ext 8) by lia.
  destruct (zlt i (8 - k)) as [HL | HG].
  - rewrite zlt_true by (change (i + (56 + k) < 64); lia).
    rewrite crossing_low_bits by lia. rewrite zlt_false by lia.
    rewrite zlt_true by lia.
    rewrite Int64.testbit_repr by exact HI.
    replace (i + (56 + k) - (56 + k)) with i by lia. reflexivity.
  - rewrite zlt_false by (change (i + (56 + k) >= 64); lia).
    rewrite orb_false_r.
    rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i 8) as [HL8 | HG8].
    + rewrite zlt_true by lia.
      rewrite crossing_high_bits by lia. rewrite zlt_true by lia.
      rewrite Int64.testbit_repr by exact HI.
      replace (i - (8 - k) + (8 - k)) with i by lia. reflexivity.
    + rewrite zlt_false by lia. reflexivity.
Qed.

Lemma crossing_byte_decode k old x :
  1 <= k <= 7 ->
  decode_word8 (crossing_byte k (crossing_high k old x) (crossing_low k x)) =
    decode_word8 (Int64.repr (Int.unsigned x)).
Proof.
  intros HK. rewrite crossing_byte_projection by exact HK.
  apply decode_word8_projection.
Qed.

Lemma crossing_high_prefix k old x :
  1 <= k <= 7 -> word_outside_eq 0 k (crossing_high k old x) old.
Proof.
  intros HK i HI Houtside. rewrite crossing_high_bits by assumption.
  rewrite zlt_false by lia. reflexivity.
Qed.

(** Bit interpretation of a byte written at a nonzero in-word cursor. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_word_bits C.jet_frame_arith C.jet_frame_spec C.jet_write8_position.
Local Open Scope Z_scope.

Lemma put_byte_bits cursor old payload i :
  8 <= cursor <= 64 -> 0 <= i < 64 ->
  Int64.testbit (put_byte cursor old payload) i =
    if zlt i cursor then
      if zlt i (cursor - 8) then false
      else Int64.testbit payload (i - (cursor - 8))
    else Int64.testbit old i.
Proof.
  intros HC HI. unfold put_byte.
  rewrite Int64.bits_or by exact HI.
  rewrite clear_low_bits by lia.
  rewrite Int64.bits_shl by exact HI.
  rewrite cursor_unsigned by lia.
  destruct (zlt i (cursor - 8)) as [HL|HG].
  - rewrite zlt_true by lia. reflexivity.
  - rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i cursor) as [HL|HG'].
    + rewrite zlt_true by lia. reflexivity.
    + rewrite zlt_false by lia. apply orb_false_r.
Qed.

Lemma put_byte_projection cursor old payload :
  8 <= cursor <= 64 ->
  Int64.zero_ext 8
    (Int64.shru (put_byte cursor old payload) (Int64.repr (cursor - 8))) =
  Int64.zero_ext 8 payload.
Proof.
  intros HC. apply Int64.same_bits_eq. intros i HI.
  change (0 <= i < 64) in HI.
  rewrite !Int64.bits_zero_ext by lia.
  destruct (zlt i 8) as [HL|HG]; [|reflexivity].
  rewrite Int64.bits_shru by exact HI.
  rewrite cursor_unsigned by lia.
  rewrite zlt_true by (change (i + (cursor - 8) < 64); lia).
  rewrite put_byte_bits by lia.
  rewrite zlt_true by lia. rewrite zlt_false by lia.
  f_equal; lia.
Qed.

Lemma put_byte_prefix cursor old payload :
  8 <= cursor <= 64 ->
  word_outside_eq 0 cursor (put_byte cursor old payload) old.
Proof.
  intros HC i HI [HL|HG]; [lia|].
  rewrite put_byte_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.


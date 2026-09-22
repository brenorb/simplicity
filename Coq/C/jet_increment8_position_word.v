(** Symbolic interpretation of increment's non-crossing output slice. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_spec C.jet_read8 C.jet_increment8 C.jet_increment8_spec.
Require Import C.jet_increment8_updates C.jet_increment8_word.
Require Import C.jet_increment8_position_update C.jet_frame_arith C.jet_frame_spec.
Require Import C.jet_word_bits C.jet_word_decode C.jet_word_position C.jet_write8_position.
Local Open Scope Z_scope.

Lemma increment8_carry_at_bit cursor old r :
  1 <= cursor <= 64 ->
  Int64.testbit (increment8_carry_at cursor old r) (cursor - 1) =
    Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r).
Proof.
  intros HC. unfold increment8_carry_at.
  destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  - rewrite Int64.bits_or by (change (0 <= cursor - 1 < 64); lia).
    rewrite Int64.bits_shl by (change (0 <= cursor - 1 < 64); lia).
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    replace (cursor - 1 - (cursor - 1)) with 0 by lia.
    change (orb (Int64.testbit old (cursor - 1)) true = true).
    apply orb_true_r.
  - rewrite clear_low_bits by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma increment8_word_at_decode cursor old r :
  9 <= cursor <= 64 ->
  decode_increment8
    (Int64.shru (increment8_word_at cursor old r) (Int64.repr (cursor - 9))) =
  decode_increment8 (increment8_word_update old r).
Proof.
  intros HC.
  assert (HB : Int64.testbit
      (Int64.shru (increment8_word_at cursor old r) (Int64.repr (cursor - 9))) 8 =
      Int64.testbit (increment8_word_update old r) 8).
  { rewrite Int64.bits_shru by (change (0 <= 8 < 64); lia).
    rewrite cursor_unsigned by lia.
    rewrite zlt_true by (change (8 + (cursor - 9) < 64); lia).
    replace (8 + (cursor - 9)) with (cursor - 1) by lia.
    unfold increment8_word_at, increment8_word_update.
    rewrite put_byte_bits by lia. rewrite zlt_false by lia.
    rewrite put_low_bits by lia.
    change (Int64.testbit (increment8_carry_at cursor old r) (cursor - 1) =
      Int64.testbit (increment8_carry_update old r) 8).
    rewrite increment8_carry_at_bit by lia.
    rewrite increment8_carry_update_bit8. reflexivity. }
  assert (HL : decode_word8
      (Int64.shru (increment8_word_at cursor old r) (Int64.repr (cursor - 9))) =
      decode_word8 (increment8_word_update old r)).
  { unfold increment8_word_at, increment8_word_update.
    replace (cursor - 9) with (cursor - 1 - 8) by lia.
    rewrite <- decode_word8_projection, put_byte_projection by lia.
    rewrite decode_word8_projection, decode_word8_put. reflexivity. }
  unfold decode_increment8. rewrite HB, HL. reflexivity.
Qed.

Lemma increment8_word_at_prefix cursor old r :
  9 <= cursor <= 64 ->
  word_outside_eq 0 cursor (increment8_word_at cursor old r) old.
Proof.
  intros HC i HI [HL|HG]; [lia|].
  unfold increment8_word_at. rewrite put_byte_bits by lia.
  rewrite zlt_false by lia. unfold increment8_carry_at.
  destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  - rewrite Int64.bits_or by exact HI.
    rewrite Int64.bits_shl by exact HI.
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    rewrite Int64.bits_one.
    destruct (zeq (i - (cursor - 1)) 0); [lia | apply orb_false_r].
  - rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

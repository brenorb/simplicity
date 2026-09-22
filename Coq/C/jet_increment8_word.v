(** Arbitrary padding and output-word contents: representation lemmas for the
    actual read8/carry/write8 data path, connected to its Simplicity term. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word C.jet_spec C.jet_read8 C.jet_increment8.
Require Import C.jet_increment8_exec C.jet_increment8_spec.
Require Import C.jet_word_bits C.jet_word_decode C.jet_frame_spec.
Local Open Scope Z_scope.

Definition increment8_carry_update (old : int64) (r : int) : int64 :=
  if Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)
  then Int64.or old (Int64.repr 256) else clear_low 9 old.

Definition increment8_word_update (old : int64) (r : int) : int64 :=
  put_low 8 (increment8_carry_update old r)
    (Int64.repr (Int.unsigned (increment8_byte r))).

Lemma increment8_word_update_zero r :
  increment8_word_update Int64.zero r = increment8_written_word r.
Proof.
  unfold increment8_word_update, increment8_carry_update, put_low,
    increment8_written_word, increment8_carry_word.
  rewrite Int64.zero_ext_and by lia.
  destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r));
    reflexivity.
Qed.

Lemma increment8_carry_update_bit8 old r :
  Int64.testbit (increment8_carry_update old r) 8 =
    Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r).
Proof.
  unfold increment8_carry_update.
  destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  - rewrite Int64.bits_or by (change (0 <= 8 < 64); lia).
    change (orb (Int64.testbit old 8) true = true). apply orb_true_r.
  - rewrite clear_low_bits by lia. reflexivity.
Qed.

Lemma increment8_word_update_decode old r :
  decode_increment8 (increment8_word_update old r) =
    decode_increment8 (increment8_written_word r).
Proof.
  rewrite <- increment8_word_update_zero.
  assert (HB : Int64.testbit (increment8_word_update old r) 8 =
      Int64.testbit (increment8_word_update Int64.zero r) 8).
  { unfold increment8_word_update. rewrite !put_low_bits by lia.
    change (Int64.testbit (increment8_carry_update old r) 8 =
      Int64.testbit (increment8_carry_update Int64.zero r) 8).
    rewrite !increment8_carry_update_bit8. reflexivity. }
  assert (HL : decode_word8 (increment8_word_update old r) =
      decode_word8 (increment8_word_update Int64.zero r)).
  { unfold increment8_word_update. rewrite !decode_word8_put. reflexivity. }
  unfold decode_increment8. rewrite HB, HL. reflexivity.
Qed.

Lemma increment8_word_update_outside old r :
  word_outside_eq 0 9 (increment8_word_update old r) old.
Proof.
  intros i Hi Hout.
  unfold increment8_word_update. rewrite put_low_bits by lia.
  rewrite zlt_false by lia. unfold increment8_carry_update.
  destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  - rewrite Int64.bits_or by exact Hi.
    change (Int64.repr 256) with (Int64.shl Int64.one (Int64.repr 8)).
    rewrite Int64.bits_shl by exact Hi.
    change (Int64.unsigned (Int64.repr 8)) with 8.
    rewrite zlt_false by lia. rewrite Int64.bits_one.
    destruct (zeq (i - 8) 0); [lia | apply orb_false_r].
  - rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Lemma encode_decode_word8 w :
  encode_word8 (decode_word8 w) = Int64.zero_ext 8 w.
Proof.
  unfold encode_word8, decode_word8. rewrite to_fromZ.
  transitivity (Int64.repr (Int64.unsigned (Int64.zero_ext 8 w))).
  - rewrite Int64.zero_ext_mod by (change (0 <= 8 < 64); lia). reflexivity.
  - apply Int64.repr_unsigned.
Qed.

Lemma read8_result_projection w : read8_result (Int64.zero_ext 8 w) = read8_result w.
Proof.
  unfold read8_result.
  assert (HM : forall v, Int64.and v (Int64.repr 255) = Int64.zero_ext 8 v).
  { intros v. symmetry. exact (Int64.zero_ext_and 8 v ltac:(lia)). }
  rewrite !HM.
  rewrite Int64.zero_ext_idem by lia. reflexivity.
Qed.

Lemma increment8_word_update_spec old input :
  decode_increment8 (increment8_word_update old (read8_result input)) =
    increment8_spec_value (decode_word8 input).
Proof.
  rewrite increment8_word_update_decode.
  rewrite <- read8_result_projection.
  rewrite <- encode_decode_word8. apply increment8_output_denotes_spec.
Qed.

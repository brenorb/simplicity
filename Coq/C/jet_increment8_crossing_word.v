(** The canonical increment value bridge for a split carry/byte output. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_increment8 C.jet_increment8_spec.
Require Import C.jet_increment8_word C.jet_increment8_updates C.jet_word_bits C.jet_word_decode.
Require Import C.jet_crossing_word.
Local Open Scope Z_scope.

Definition decode_carry_crossing k high low : Ty.tySem (Ty.Prod Bit Word8) :=
  ((if Int64.testbit high k then inr tt else inl tt),
    decode_word8 (crossing_byte k high low)).

Lemma increment8_carry_byte_spec input :
  ((if Int.ltu (Int.sub (Int.repr 255) (Int.repr 1))
      (increment8_u (read8_result input)) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned (increment8_byte (read8_result input))))) =
  @increment8_spec Alg.CoreFunSem (decode_word8 input).
Proof.
  pose proof (increment8_word_update_spec Int64.zero input) as H.
  unfold decode_increment8 in H.
  assert (HB : Int64.testbit (increment8_word_update Int64.zero (read8_result input)) 8 =
      Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u (read8_result input))).
  { unfold increment8_word_update. rewrite put_low_bits by lia.
    apply increment8_carry_update_bit8. }
  rewrite HB in H. unfold increment8_word_update in H.
  rewrite decode_word8_put in H. exact H.
Qed.

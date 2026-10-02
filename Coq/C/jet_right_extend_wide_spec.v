(** Canonical right-extension bridge for the actual wide input family. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jet_spec C.jet_encoding C.jet_word_bit_spec C.jet_int64_bit_mask.
Require Import C.jet_extend_word_spec C.jet_right_extend_word_spec.
Require Import C.jet_wide C.jet_wide_spec C.jet_pad_bit_spec C.jet_write_wide_sequence.
Require Import C.jet_extend_wide_loop C.jet_extend_wide_exec C.jet_extend_wide_spec.
Require Import C.jet_right_extend_wide_loop.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma right_extend_wide_lsb_denotes s (x : Ty.tySem (Word (wide_log (extend_wide_input s)))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log (extend_wide_input s))) x ->
  right_extend_wide_lsb r = Bit.toBool (@Word.rightmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x).
Proof.
  intros Hr. unfold right_extend_wide_lsb.
  change (negb (Int64.eq (Int64.and r (Int64.repr (2 ^ 0))) Int64.zero) =
    Bit.toBool (@Word.rightmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x)).
  rewrite int64_single_bit_mask_nonzero by lia. unfold Int64.testbit; rewrite Hr.
  destruct s.
  - change (Z.testbit (@toZ (WordToZ 4) x) 0 = Bit.toBool (@word_bit_spec 4 0 Alg.CoreFunSem x)).
    symmetry; apply word_bit_spec_numeric; cbn; lia.
  - change (Z.testbit (@toZ (WordToZ 4) x) 0 = Bit.toBool (@word_bit_spec 4 0 Alg.CoreFunSem x)).
    symmetry; apply word_bit_spec_numeric; cbn; lia.
  - change (Z.testbit (@toZ (WordToZ 5) x) 0 = Bit.toBool (@word_bit_spec 5 0 Alg.CoreFunSem x)).
    symmetry; apply word_bit_spec_numeric; cbn; lia.
Qed.

Definition right_extend_wide_output_args s r := [r] ++
  repeat (extend_bit_long (extend_wide_input s) (right_extend_wide_lsb r))
    (Z.to_nat (extend_wide_count s)).
Lemma right_extend_wide_args_length s r :
  wide_bits (extend_wide_input s) * Z.of_nat (length (right_extend_wide_output_args s r)) = extend_wide_bits s.
Proof. unfold right_extend_wide_output_args; rewrite app_length, repeat_length; destruct s; reflexivity. Qed.

Lemma right_extend_wide_sequence_denotes s (x : Ty.tySem (Word (wide_log (extend_wide_input s)))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log (extend_wide_input s))) x ->
  wide_sequence_cells (extend_wide_input s) (right_extend_wide_output_args s r) =
    encode (@right_extend_word_spec (wide_log (extend_wide_input s)) (extend_wide_depth s) Alg.CoreFunSem x).
Proof.
  intros Hr. unfold wide_sequence_cells, right_extend_wide_output_args.
  rewrite map_app, concat_app, map_repeat. cbn [map concat]. rewrite app_nil_r.
  rewrite extend_wide_constant_decode, (extend_wide_payload_decode s x r Hr).
  pose proof (right_extend_wide_lsb_denotes s x r Hr) as HB.
  change (encode x ++ concat (repeat
    (encode (@pad_word_constant (wide_log (extend_wide_input s)) (right_extend_wide_lsb r) Alg.CoreFunSem tt))
    (Z.to_nat (extend_wide_count s))) =
    encode (match @Word.rightmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x with
      | inl _ => @right_pad_word_spec (wide_log (extend_wide_input s)) (extend_wide_depth s) Datatypes.false Alg.CoreFunSem x
      | inr _ => @right_pad_word_spec (wide_log (extend_wide_input s)) (extend_wide_depth s) Datatypes.true Alg.CoreFunSem x end)).
  destruct (@Word.rightmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x) as [[]|[]] eqn:Hbit;
    cbn [Bit.toBool] in HB; rewrite HB;
    rewrite encode_right_pad_word_spec; destruct s; reflexivity.
Qed.

(** Symbolic machine-to-canonical-program bridge for wide left extensions.
    No input enumeration; the machine carrier is constrained by the reader's
    exact unsigned result, not merely by lossy logical decoding. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jet_encoding C.jet_word_repr C.jet_word_bit_spec C.jet_int64_bit_mask.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec C.jet_pad_bit_spec.
Require Import C.jet_extend_word_spec C.jet_extend_wide_loop C.jet_extend_wide_exec.
Require Import C.jet_write_wide_sequence.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition extend_wide_depth s := match s with E16to32 => 1%nat | E16to64 => 2%nat | E32to64 => 1%nat end.
Lemma extend_wide_args_length s r :
  wide_bits (extend_wide_input s) * Z.of_nat (length (extend_wide_output_args s r)) = extend_wide_bits s.
Proof. unfold extend_wide_output_args; rewrite app_length, repeat_length; destruct s; reflexivity. Qed.

Lemma extend_wide_msb_denotes s (x : Ty.tySem (Word (wide_log (extend_wide_input s)))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log (extend_wide_input s))) x ->
  extend_wide_msb s r = Bit.toBool (@Word.leftmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x).
Proof.
  intros Hr.
  assert (HX : 0 <= @toZ (WordToZ (wide_log (extend_wide_input s))) x <
    2 ^ wide_bits (extend_wide_input s)) by (destruct s; apply word_toZ_range).
  assert (HB : Bit.toBool (@Word.leftmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x) =
    Z.testbit (@toZ (WordToZ (wide_log (extend_wide_input s))) x) (wide_bits (extend_wide_input s) - 1)).
  { destruct s.
    - change (Bit.toBool (@word_bit_spec 4 15 Alg.CoreFunSem x) = Z.testbit (@toZ (WordToZ 4) x) 15).
      apply word_bit_spec_numeric; cbn; lia.
    - change (Bit.toBool (@word_bit_spec 4 15 Alg.CoreFunSem x) = Z.testbit (@toZ (WordToZ 4) x) 15).
      apply word_bit_spec_numeric; cbn; lia.
    - change (Bit.toBool (@word_bit_spec 5 31 Alg.CoreFunSem x) = Z.testbit (@toZ (WordToZ 5) x) 31).
      apply word_bit_spec_numeric; cbn; lia. }
  assert (Hk : 0 <= wide_bits (extend_wide_input s) - 1) by (destruct s; cbn; lia).
  assert (HXtop : 0 <= @toZ (WordToZ (wide_log (extend_wide_input s))) x <
    2 ^ (wide_bits (extend_wide_input s) - 1 + 1)).
  { replace (wide_bits (extend_wide_input s) - 1 + 1) with (wide_bits (extend_wide_input s)) by lia; exact HX. }
  rewrite HB, (top_bit_threshold _ _ Hk HXtop).
  unfold extend_wide_msb. rewrite Int64.shru_div_two_p, Int64.unsigned_repr by
    (destruct s; change Int64.max_unsigned with 18446744073709551615; cbn; lia).
  rewrite Hr, two_p_equiv by lia.
  change (negb (Int64.eq (Int64.repr (@toZ (WordToZ (wide_log (extend_wide_input s))) x /
    2 ^ (wide_bits (extend_wide_input s) - 1))) Int64.zero) =
    negb (@toZ (WordToZ (wide_log (extend_wide_input s))) x <? 2 ^ (wide_bits (extend_wide_input s) - 1))).
  assert (HD : 0 < 2 ^ (wide_bits (extend_wide_input s) - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdouble : 2 ^ wide_bits (extend_wide_input s) = 2 * 2 ^ (wide_bits (extend_wide_input s) - 1))
    by (destruct s; reflexivity).
  destruct (@toZ (WordToZ (wide_log (extend_wide_input s))) x <? 2 ^ (wide_bits (extend_wide_input s) - 1)) eqn:HL.
  - apply Z.ltb_lt in HL. rewrite Z.div_small by lia; reflexivity.
  - apply Z.ltb_ge in HL.
    assert (HQ : @toZ (WordToZ (wide_log (extend_wide_input s))) x /
      2 ^ (wide_bits (extend_wide_input s) - 1) = 1).
    { symmetry. apply Z.div_unique with (r := @toZ (WordToZ (wide_log (extend_wide_input s))) x -
        2 ^ (wide_bits (extend_wide_input s) - 1)); rewrite Hdouble in HX; lia. }
    rewrite HQ; reflexivity.
Qed.

Lemma extend_wide_constant_decode s bit :
  decode_wide (extend_wide_input s) (Int64.zero_ext (wide_bits (extend_wide_input s))
    (extend_bit_long (extend_wide_input s) bit)) =
  @pad_word_constant (wide_log (extend_wide_input s)) bit Alg.CoreFunSem tt.
Proof. destruct s, bit; vm_compute; reflexivity. Qed.

Lemma extend_wide_payload_decode s (x : Ty.tySem (Word (wide_log (extend_wide_input s)))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log (extend_wide_input s))) x ->
  decode_wide (extend_wide_input s) (Int64.zero_ext (wide_bits (extend_wide_input s)) r) = x.
Proof.
  intros Hr. unfold decode_wide.
  rewrite Int64.zero_ext_mod by (destruct s; change Int64.zwordsize with 64; cbn; lia).
  rewrite Hr, two_p_equiv by (destruct s; cbn; lia).
  replace (wide_bits (extend_wide_input s)) with (Z.of_nat (Nat.pow 2 (wide_log (extend_wide_input s))))
    by (destruct s; reflexivity).
  rewrite word_fromZ_mod. apply from_toZ.
Qed.

Lemma extend_wide_sequence_denotes s (x : Ty.tySem (Word (wide_log (extend_wide_input s)))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log (extend_wide_input s))) x ->
  wide_sequence_cells (extend_wide_input s) (extend_wide_output_args s r) =
    encode (@left_extend_word_spec (wide_log (extend_wide_input s)) (extend_wide_depth s) Alg.CoreFunSem x).
Proof.
  intros Hr. unfold wide_sequence_cells, extend_wide_output_args.
  rewrite map_app, concat_app, map_repeat. cbn [map concat]. rewrite app_nil_r.
  rewrite extend_wide_constant_decode, (extend_wide_payload_decode s x r Hr).
  pose proof (extend_wide_msb_denotes s x r Hr) as HB.
  change (concat (repeat
    (encode (@pad_word_constant (wide_log (extend_wide_input s)) (extend_wide_msb s r) Alg.CoreFunSem tt))
    (Z.to_nat (extend_wide_count s))) ++ encode x =
    encode (match @Word.leftmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x with
      | inl _ => @left_pad_word_spec (wide_log (extend_wide_input s)) (extend_wide_depth s) Datatypes.false Alg.CoreFunSem x
      | inr _ => @left_pad_word_spec (wide_log (extend_wide_input s)) (extend_wide_depth s) Datatypes.true Alg.CoreFunSem x end)).
  destruct (@Word.leftmost Bit (wide_log (extend_wide_input s)) Alg.CoreFunSem x) as [[]|[]] eqn:Hbit;
    cbn [Bit.toBool] in HB; rewrite HB;
    rewrite encode_left_pad_word_spec; destruct s; reflexivity.
Qed.

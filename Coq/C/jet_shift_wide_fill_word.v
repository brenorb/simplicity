(** Shared wide fill-XOR bridges. Exact complement representation applies
    to initial word-sized carriers; arbitrary intermediate carriers expose
    only the low-bit complement fact required after a left shift. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_encoding C.jet_word_repr C.jet_complement_spec C.jet_shift_wide_expr.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift_wide_fill_mask_low s :
  shift_wide_fill_mask s = Int64.zero_ext (wide_bits s) Int64.mone.
Proof.
  destruct s; [reflexivity|reflexivity|].
  symmetry. apply Int64.zero_ext_above. change (64 >= 64); lia.
Qed.

Lemma shift_wide_fill_result_bits s r j : 0 <= j < wide_bits s ->
  Int64.testbit (shift_wide_fill_result s r) j = negb (Int64.testbit r j).
Proof.
  intros Hj. pose proof (wide_bits_bounds s) as HW.
  unfold shift_wide_fill_result. rewrite Int64.bits_xor by (change Int64.zwordsize with 64; lia).
  rewrite shift_wide_fill_mask_low, Int64.bits_zero_ext, (zlt_true _ j (wide_bits s)) by lia.
  rewrite Int64.bits_mone by (change Int64.zwordsize with 64; lia).
  destruct (Int64.testbit r j); reflexivity.
Qed.

Lemma shift_wide_fill_result_repr s (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  shift_wide_fill_result s r =
    Int64.repr (@toZ (WordToZ (wide_log s)) (@complement_spec (wide_log s) Alg.CoreFunSem x)).
Proof.
  intros HR. apply Int64.same_bits_eq. intros j Hj.
  change (0 <= j < 64) in Hj. rewrite Int64.testbit_repr by exact Hj.
  destruct (Z_lt_ge_dec j (wide_bits s)) as [HL|HH].
  - rewrite shift_wide_fill_result_bits by lia.
    rewrite complement_spec_bits by (destruct s; exact (conj (proj1 Hj) HL)).
    unfold Int64.testbit. rewrite HR; reflexivity.
  - unfold shift_wide_fill_result. rewrite Int64.bits_xor by exact Hj.
    rewrite shift_wide_fill_mask_low, Int64.bits_zero_ext, (zlt_false _ j (wide_bits s)) by lia.
    unfold Int64.testbit. rewrite HR.
    rewrite word_toZ_high_bits by (rewrite <- wide_bits_pow; lia).
    symmetry. apply word_toZ_high_bits. rewrite <- wide_bits_pow; lia.
Qed.

Lemma shift_wide_fill_result_unsigned s (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  Int64.unsigned (shift_wide_fill_result s r) =
    @toZ (WordToZ (wide_log s)) (@complement_spec (wide_log s) Alg.CoreFunSem x).
Proof.
  intros HR. rewrite (shift_wide_fill_result_repr s x r HR). apply Int64.unsigned_repr.
  pose proof (word_toZ_range (wide_log s) (@complement_spec (wide_log s) Alg.CoreFunSem x)) as H.
  rewrite <- wide_bits_pow in H.
  destruct s; cbn [wide_bits] in H; change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

(** Symbolic low-bit bridge for the actual LP64 wide shift/count branch.
    Counts are not reduced modulo the logical width. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_encoding C.jet_word_repr C.jet_rotate_control_word.
Require Import C.jet_shift_wide_expr C.jet_shift_wide_helper_exec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift_wide_count_result_bits s right (x : Ty.tySem (Word (wide_log s))) r a j :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x -> 0 <= j < wide_bits s ->
  Int64.testbit (shift_wide_count_result s right r a) j =
    Z.testbit (@toZ (WordToZ (wide_log s)) x)
      (j - rotate_signed_amount right (Int.unsigned a)).
Proof.
  intros HR Hj. pose proof (Int.unsigned_range a) as HA.
  pose proof (wide_bits_bounds s) as HW.
  assert (HU : Int64.unsigned (Int64.repr (Int.unsigned a)) = Int.unsigned a).
  { apply Int64.unsigned_repr. change Int.max_unsigned with 4294967295 in HA.
    change Int.modulus with 4294967296 in HA.
    change Int64.max_unsigned with 18446744073709551615; lia. }
  unfold shift_wide_count_result. destruct (zlt (Int.unsigned a) (wide_bits s)) as [HL|HG].
  - unfold shift_wide_scalar_result. destruct right; cbn [rotate_signed_amount].
    + rewrite Int64.bits_shru by (change Int64.zwordsize with 64; lia).
      rewrite HU. destruct (zlt (j + Int.unsigned a) Int64.zwordsize) as [Hlow|Hhigh].
      * unfold Int64.testbit. rewrite HR. f_equal; lia.
      * symmetry. apply word_toZ_high_bits. rewrite <- wide_bits_pow.
        change Int64.zwordsize with 64 in Hhigh; lia.
    + rewrite Int64.bits_shl by (change Int64.zwordsize with 64; lia).
      rewrite HU. destruct (zlt j (Int.unsigned a)) as [Hsmall|Hlarge].
      * symmetry. apply Z.testbit_neg_r; lia.
      * unfold Int64.testbit. rewrite HR; reflexivity.
  - rewrite Int64.bits_zero. destruct right; cbn [rotate_signed_amount].
    + symmetry. apply word_toZ_high_bits. rewrite <- wide_bits_pow; lia.
    + symmetry. apply Z.testbit_neg_r; lia.
Qed.

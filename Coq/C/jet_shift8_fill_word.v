(** Exact byte fill-toggle representation for the shared C shift helper.
    Used by forthcoming fill-input jet consumers, not jet coverage itself. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_repr C.jet_complement_spec C.jet_shift8_expr.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma complement_spec_involutive n (x : Ty.tySem (Word n)) :
  @complement_spec n Alg.CoreFunSem (@complement_spec n Alg.CoreFunSem x) = x.
Proof.
  induction n as [|n IH].
  - destruct x as [[]|[]]; reflexivity.
  - destruct x as [hi lo]. change
      ((@complement_spec n Alg.CoreFunSem (@complement_spec n Alg.CoreFunSem hi),
        @complement_spec n Alg.CoreFunSem (@complement_spec n Alg.CoreFunSem lo)) = (hi,lo)).
    rewrite !IH; reflexivity.
Qed.

Lemma low_byte_mask_bit j : 0 <= j < 8 -> Int.testbit (Int.repr 255) j = Datatypes.true.
Proof.
  intros Hj. change (Int.repr 255) with (Int.zero_ext 8 Int.mone).
  rewrite Int.bits_zero_ext, (zlt_true _ j 8) by lia.
  apply Int.bits_mone. change (0 <= j < 32); lia.
Qed.

Lemma shift8_fill_result_bits r j : 0 <= j < 8 ->
  Int.testbit (shift8_fill_result r) j = negb (Int.testbit r j).
Proof.
  intros Hj. unfold shift8_fill_result.
  rewrite Int.bits_zero_ext, (zlt_true _ j 8) by lia.
  rewrite Int.bits_xor by (change Int.zwordsize with 32; lia).
  rewrite low_byte_mask_bit by exact Hj. destruct (Int.testbit r j); reflexivity.
Qed.

Lemma shift8_fill_result_repr (x : Ty.tySem (Word 3)) r :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  shift8_fill_result r = Int.repr (@toZ (WordToZ 3) (@complement_spec 3 Alg.CoreFunSem x)).
Proof.
  intros HR. apply Int.same_bits_eq. intros j Hj. change (0 <= j < 32) in Hj.
  rewrite Int.testbit_repr by exact Hj.
  destruct (Z_lt_ge_dec j 8) as [HL|HH].
  - rewrite shift8_fill_result_bits by lia.
    rewrite complement_spec_bits by (change (0 <= j < 8); lia).
    unfold Int.testbit. rewrite HR; reflexivity.
  - unfold shift8_fill_result. rewrite Int.bits_zero_ext, (zlt_false _ j 8) by lia.
    symmetry. apply word_toZ_high_bits. change (8 <= j); lia.
Qed.

Lemma shift8_fill_result_unsigned (x : Ty.tySem (Word 3)) r :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  Int.unsigned (shift8_fill_result r) = @toZ (WordToZ 3) (@complement_spec 3 Alg.CoreFunSem x).
Proof.
  intros HR. rewrite (shift8_fill_result_repr x r HR). apply Int.unsigned_repr.
  pose proof (word_toZ_range 3 (@complement_spec 3 Alg.CoreFunSem x)) as HC.
  change (0 <= @toZ (WordToZ 3) (@complement_spec 3 Alg.CoreFunSem x) < 256) in HC.
  change Int.max_unsigned with 4294967295; lia.
Qed.

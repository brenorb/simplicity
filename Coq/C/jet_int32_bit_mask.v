(** Width-32 symbolic isolated-bit masks, shared by byte/int C expressions.
    These carrier lemmas alone are not jet implementation equivalence. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma int32_single_bit_mask r k :
  0 <= k < 32 ->
  Int.and r (Int.repr (2 ^ k)) =
    if Int.testbit r k then Int.repr (2 ^ k) else Int.zero.
Proof.
  intros Hk. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_and by exact Hi.
  rewrite Int.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
  destruct (k =? i) eqn:HE.
  - apply Z.eqb_eq in HE. subst i. destruct (Int.testbit r k); cbn [andb].
    + rewrite Int.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
      rewrite Z.eqb_refl. reflexivity.
    + rewrite Int.bits_zero. reflexivity.
  - rewrite andb_false_r. destruct (Int.testbit r k).
    + rewrite Int.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
      rewrite HE. reflexivity.
    + rewrite Int.bits_zero. reflexivity.
Qed.

Lemma int32_single_bit_mask_nonzero r k :
  0 <= k < 32 ->
  negb (Int.eq (Int.and r (Int.repr (2 ^ k))) Int.zero) = Int.testbit r k.
Proof.
  intros Hk. rewrite int32_single_bit_mask by exact Hk.
  destruct (Int.testbit r k).
  - assert (HP : 0 < 2 ^ k < Int.modulus).
    { change Int.modulus with (2 ^ 32). split.
      - apply Z.pow_pos_nonneg; lia.
      - apply Z.pow_lt_mono_r; lia. }
    assert (HM : Int.max_unsigned = Int.modulus - 1) by reflexivity.
    unfold Int.eq. rewrite Int.unsigned_repr by lia.
    change (Int.unsigned Int.zero) with 0.
    rewrite zeq_false by lia. reflexivity.
  - rewrite Int.eq_true. reflexivity.
Qed.

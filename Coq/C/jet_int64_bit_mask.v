(** Symbolic carrier bridges for top-bit tests and isolated-bit Boolean masks.
    These prepare parse_sequence and other bit-selecting C bodies. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma top_bit_threshold z k :
  0 <= k -> 0 <= z < 2 ^ (k + 1) ->
  Z.testbit z k = negb (z <? 2 ^ k).
Proof.
  intros Hk Hz. assert (HP : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (HS : 2 ^ (k + 1) = 2 * 2 ^ k).
  { rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
  rewrite HS in Hz. destruct (z <? 2 ^ k) eqn:HL.
  - apply Z.ltb_lt in HL. cbn [negb]. apply Bool.not_true_is_false.
    intros HT. apply Z.testbit_true in HT; [|exact Hk].
    rewrite Z.div_small in HT by lia. discriminate HT.
  - apply Z.ltb_ge in HL. cbn [negb]. apply Z.testbit_true; [exact Hk|].
    assert (HQ : z / 2 ^ k = 1).
    { symmetry. apply Z.div_unique with (r := z - 2 ^ k); nia. }
    rewrite HQ. reflexivity.
Qed.

Lemma int64_single_bit_mask r k :
  0 <= k < 64 ->
  Int64.and r (Int64.repr (2 ^ k)) =
    if Int64.testbit r k then Int64.repr (2 ^ k) else Int64.zero.
Proof.
  intros Hk. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and by exact Hi.
  rewrite Int64.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
  destruct (k =? i) eqn:HE.
  - apply Z.eqb_eq in HE. subst i. destruct (Int64.testbit r k); cbn [andb].
    + rewrite Int64.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
      rewrite Z.eqb_refl. reflexivity.
    + rewrite Int64.bits_zero. reflexivity.
  - rewrite andb_false_r. destruct (Int64.testbit r k).
    + rewrite Int64.testbit_repr by exact Hi. rewrite Z.pow2_bits_eqb by lia.
      rewrite HE. reflexivity.
    + rewrite Int64.bits_zero. reflexivity.
Qed.

Lemma int64_single_bit_mask_nonzero r k :
  0 <= k < 64 ->
  negb (Int64.eq (Int64.and r (Int64.repr (2 ^ k))) Int64.zero) = Int64.testbit r k.
Proof.
  intros Hk. rewrite int64_single_bit_mask by exact Hk.
  destruct (Int64.testbit r k).
  - assert (HP : 0 < 2 ^ k < Int64.modulus).
    { change Int64.modulus with (2 ^ 64). split.
      - apply Z.pow_pos_nonneg; lia.
      - apply Z.pow_lt_mono_r; lia. }
    assert (HM : Int64.max_unsigned = Int64.modulus - 1) by reflexivity.
    unfold Int64.eq. rewrite Int64.unsigned_repr by lia.
    change (Int64.unsigned Int64.zero) with 0.
    rewrite zeq_false by lia. reflexivity.
  - rewrite Int64.eq_true. reflexivity.
Qed.

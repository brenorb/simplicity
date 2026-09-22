(** Symbolic word algebra for the actual LSBclear shift sequence. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Local Open Scope Z_scope.

Definition clear_low (n : Z) (w : int64) : int64 :=
  Int64.shl (Int64.shl
    (Int64.shru (Int64.shru w (Int64.repr 1)) (Int64.repr (n - 1)))
    (Int64.repr 1)) (Int64.repr (n - 1)).

Definition put_low (n : Z) (old payload : int64) : int64 :=
  Int64.or (clear_low n old) (Int64.zero_ext n payload).

Lemma clear_low_bits n w i :
  1 <= n <= 64 -> 0 <= i < 64 ->
  Int64.testbit (clear_low n w) i =
    if zlt i n then false else Int64.testbit w i.
Proof.
  intros Hn Hi. unfold clear_low.
  assert (UN : Int64.unsigned (Int64.repr (n - 1)) = n - 1).
  { apply Int64.unsigned_repr. change (0 <= n - 1 <= 18446744073709551615). lia. }
  assert (U1 : Int64.unsigned (Int64.repr 1) = 1) by reflexivity.
  rewrite Int64.bits_shl by exact Hi. rewrite UN.
  destruct (zlt i (n - 1)) as [Hlt|Hge].
  - rewrite zlt_true by lia. reflexivity.
  - rewrite Int64.bits_shl by (change (0 <= i - (n - 1) < 64); lia).
    rewrite U1. destruct (zlt (i - (n - 1)) 1) as [Hlt|Hge1].
    + rewrite zlt_true by lia. reflexivity.
    + rewrite Int64.bits_shru by (change (0 <= i - (n - 1) - 1 < 64); lia).
      rewrite UN. rewrite zlt_true by (change (i - (n - 1) - 1 + (n - 1) < 64); lia).
      rewrite Int64.bits_shru by (change (0 <= i - (n - 1) - 1 + (n - 1) < 64); lia).
      rewrite U1. rewrite zlt_true by (change (i - (n - 1) - 1 + (n - 1) + 1 < 64); lia).
      rewrite zlt_false by lia. f_equal; lia.
Qed.

Lemma put_low_bits n old payload i :
  1 <= n <= 64 -> 0 <= i < 64 ->
  Int64.testbit (put_low n old payload) i =
    if zlt i n then Int64.testbit payload i else Int64.testbit old i.
Proof.
  intros Hn Hi. unfold put_low.
  rewrite Int64.bits_or by exact Hi.
  rewrite clear_low_bits by assumption.
  rewrite Int64.bits_zero_ext by lia.
  destruct (zlt i n); cbn; [reflexivity | apply orb_false_r].
Qed.

Lemma put_low_projection n old payload :
  1 <= n <= 64 ->
  Int64.zero_ext n (put_low n old payload) = Int64.zero_ext n payload.
Proof.
  intros Hn. apply Int64.same_bits_eq. intros i Hi.
  change (0 <= i < 64) in Hi.
  rewrite !Int64.bits_zero_ext by lia.
  rewrite put_low_bits by assumption.
  destruct (zlt i n); reflexivity.
Qed.

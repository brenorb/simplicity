(** Symbolic observations of the values stored by the two checked short-copy
    paths. These bridges support execution-to-frame proofs, not jet coverage. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_word_bits C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition copy_short_value ss ds old source :=
  if zlt ss ds then copy_left_value ss ds old source
  else copy_right_value ss ds old source.

Lemma copy_left_value_bits ss ds old source i :
  1 <= ss /\ ss < ds <= 63 -> 0 <= i < 64 ->
  Int64.testbit (copy_left_value ss ds old source) i =
    if zlt i (ds - ss) then false
    else if zlt i ds then Int64.testbit source (i - (ds - ss))
    else Int64.testbit old i.
Proof.
  intros Hrange Hi. unfold copy_left_value.
  rewrite Int64.bits_or by exact Hi.
  rewrite clear_low_bits by lia.
  rewrite Int64.bits_shl by exact Hi.
  rewrite Int64.unsigned_repr by (change (0 <= ds - ss <= 18446744073709551615); lia).
  destruct (zlt i (ds - ss)) as [Hlow|Hhigh].
  - rewrite zlt_true by lia. reflexivity.
  - rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i ds) as [Hinside|Houtside].
    + rewrite zlt_true by lia. reflexivity.
    + rewrite zlt_false by lia. apply orb_false_r.
Qed.

Lemma copy_right_value_bits ss ds old source i :
  1 <= ds <= 63 -> ds <= ss <= 64 -> 0 <= i < 64 ->
  Int64.testbit (copy_right_value ss ds old source) i =
    if zlt i ds then Int64.testbit source (i + (ss - ds))
    else Int64.testbit old i.
Proof.
  intros Hds Hss Hi. unfold copy_right_value, copy_right_payload.
  rewrite Int64.bits_or by exact Hi.
  rewrite clear_low_bits by lia.
  rewrite Int64.bits_zero_ext by lia.
  destruct (zlt i ds) as [Hinside|Houtside].
  - rewrite Int64.bits_shru by exact Hi.
    rewrite Int64.unsigned_repr by (change (0 <= ss - ds <= 18446744073709551615); lia).
    rewrite zlt_true by (change (i + (ss - ds) < 64); lia). reflexivity.
  - apply orb_false_r.
Qed.

Lemma copy_left_copied_bit ss ds n old source j :
  1 <= ss /\ ss < ds <= 63 -> 0 < n <= ss -> 0 <= j < n ->
  Int64.testbit (copy_left_value ss ds old source) (ds - 1 - j) =
    Int64.testbit source (ss - 1 - j).
Proof.
  intros Hrange Hn Hj. rewrite copy_left_value_bits by lia.
  rewrite zlt_false by lia. rewrite zlt_true by lia. f_equal; lia.
Qed.

Lemma copy_right_copied_bit ss ds n old source j :
  1 <= ds <= 63 -> ds <= ss <= 64 -> 0 < n <= ds -> 0 <= j < n ->
  Int64.testbit (copy_right_value ss ds old source) (ds - 1 - j) =
    Int64.testbit source (ss - 1 - j).
Proof.
  intros Hds Hss Hn Hj. rewrite copy_right_value_bits by lia.
  rewrite zlt_true by lia. f_equal; lia.
Qed.

Lemma copy_left_existing_bit ss ds old source i :
  1 <= ss /\ ss < ds <= 63 -> ds <= i < 64 ->
  Int64.testbit (copy_left_value ss ds old source) i = Int64.testbit old i.
Proof.
  intros Hrange Hi. rewrite copy_left_value_bits by lia.
  rewrite !zlt_false by lia; reflexivity.
Qed.

Lemma copy_right_existing_bit ss ds old source i :
  1 <= ds <= 63 -> ds <= ss <= 64 -> ds <= i < 64 ->
  Int64.testbit (copy_right_value ss ds old source) i = Int64.testbit old i.
Proof.
  intros Hds Hss Hi. rewrite copy_right_value_bits by lia.
  rewrite zlt_false by lia; reflexivity.
Qed.

Lemma copy_short_copied_bit ss ds n old source j :
  1 <= ss <= 64 -> 1 <= ds <= 63 ->
  0 < n <= ss -> n <= ds -> 0 <= j < n ->
  Int64.testbit (copy_short_value ss ds old source) (ds - 1 - j) =
    Int64.testbit source (ss - 1 - j).
Proof.
  intros Hss Hds Hn Hnd Hj. unfold copy_short_value.
  destruct (zlt ss ds).
  - apply copy_left_copied_bit with (n := n); lia.
  - apply copy_right_copied_bit with (n := n); lia.
Qed.

Lemma copy_short_existing_bit ss ds old source i :
  1 <= ss <= 64 -> 1 <= ds <= 63 -> ds <= i < 64 ->
  Int64.testbit (copy_short_value ss ds old source) i = Int64.testbit old i.
Proof.
  intros Hss Hds Hi. unfold copy_short_value.
  destruct (zlt ss ds).
  - apply copy_left_existing_bit; lia.
  - apply copy_right_existing_bit; lia.
Qed.

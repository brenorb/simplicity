(** Logical Word16 input bits and exact interpretation of the generated reader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes ClightBigstep Memory Events.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_input_layout.
Require Import C.jet_read16_layout_total C.jet_read16_layout_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma nth_error_seq_lt start n i :
  (i < n)%nat -> nth_error (seq start n) i = Some (start + i)%nat.
Proof.
  revert start i. induction n; intros start i Hi; [lia|].
  destruct i; simpl.
  - f_equal; lia.
  - rewrite IHn by lia. f_equal; lia.
Qed.

Lemma frame_input_word_bits_nth {n} (x : Ty.tySem (Word n)) i :
  (i < Nat.pow 2 n)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ n) x)
      (Z.of_nat (Nat.pow 2 n - S i))).
Proof.
  intros Hi. unfold frame_input_word_bits. rewrite nth_error_map.
  rewrite nth_error_seq_lt by exact Hi. simpl. reflexivity.
Qed.

Lemma frame_input_word_bits16_nth (x : Ty.tySem (Word 4)) i :
  (i < 16)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i)).
Proof.
  intros Hi. rewrite frame_input_word_bits_nth by exact Hi.
  assert (Hindex :
    Z.of_nat (16 - S i) = 15 - Z.of_nat i).
  { rewrite Nat2Z.inj_sub by lia. rewrite (Nat2Z.inj_succ i).
    change (16 - (Z.of_nat i + 1) = 15 - Z.of_nat i). lia. }
  cbn [Nat.pow].
  change
    (Some (Z.testbit (@toZ (WordToZ 4) x) (Z.of_nat (16 - S i))) =
     Some (Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i))).
  rewrite Hindex. reflexivity.
Qed.

Lemma frame_input_word_at_bit16 m bw edge cursor (x : Ty.tySem (Word 4)) i :
  frame_input_word_at m bw edge cursor x -> (i < 16)%nat ->
  frame_input_bit_at m bw edge (cursor + Z.of_nat i)
    (Z.testbit (@toZ (WordToZ 4) x) (15 - Z.of_nat i)).
Proof.
  intros Hinput Hi. unfold frame_input_word_at, frame_input_bits_at in Hinput.
  eapply Hinput. apply frame_input_word_bits16_nth. exact Hi.
Qed.

Lemma cursor_add_index_non_crossing cursor i :
  0 <= cursor -> 0 <= i -> cursor mod 64 + i < 64 ->
  (cursor + i) / 64 = cursor / 64 /\
  (cursor + i) mod 64 = cursor mod 64 + i.
Proof.
  intros HC HI Hr.
  assert (Hrem : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hdecomp : cursor + i = 64 * (cursor / 64) + (cursor mod 64 + i)).
  { pose proof (Z.div_mod cursor 64 ltac:(lia)). lia. }
  split.
  - symmetry. apply (Z.div_unique (cursor + i) 64 (cursor / 64)
      (cursor mod 64 + i)); [left; lia | exact Hdecomp].
  - symmetry. apply (Z.mod_unique (cursor + i) 64 (cursor / 64)
      (cursor mod 64 + i)); [left; lia | exact Hdecomp].
Qed.

Lemma cursor_add_index_crossing cursor i :
  0 <= cursor -> 0 <= i -> 64 <= cursor mod 64 + i -> cursor mod 64 + i < 128 ->
  (cursor + i) / 64 = cursor / 64 + 1 /\
  (cursor + i) mod 64 = cursor mod 64 + i - 64.
Proof.
  intros HC HI Hr Hupper.
  assert (Hrem : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hdecomp : cursor + i = 64 * (cursor / 64 + 1) +
      (cursor mod 64 + i - 64)).
  { pose proof (Z.div_mod cursor 64 ltac:(lia)). lia. }
  split.
  - symmetry. apply (Z.div_unique (cursor + i) 64 (cursor / 64 + 1)
      (cursor mod 64 + i - 64)); [left; lia | exact Hdecomp].
  - symmetry. apply (Z.mod_unique (cursor + i) 64 (cursor / 64 + 1)
      (cursor mod 64 + i - 64)); [left; lia | exact Hdecomp].
Qed.

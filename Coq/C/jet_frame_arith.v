(** Bounded cursor calculations used by the generated frame helpers. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Local Open Scope Z_scope.

Lemma cursor_unsigned n : 0 <= n <= 128 -> Int64.unsigned (Int64.repr n) = n.
Proof.
  intros Hn. apply Int64.unsigned_repr.
  change (0 <= n <= 18446744073709551615). lia.
Qed.

Lemma cursor_sub n k : 0 <= k <= n -> n <= 128 ->
  Int64.sub (Int64.repr n) (Int64.repr k) = Int64.repr (n - k).
Proof.
  intros Hnk Hn. unfold Int64.sub. rewrite !cursor_unsigned by lia. reflexivity.
Qed.

Lemma cursor_word_index n : 1 <= n <= 64 ->
  Int64.divu (Int64.sub (Int64.repr n) Int64.one) (Int64.repr 64) = Int64.zero.
Proof.
  intros Hn. change Int64.one with (Int64.repr 1).
  rewrite cursor_sub by lia. unfold Int64.divu.
  rewrite !cursor_unsigned by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma cursor_word_shift n : 1 <= n <= 64 ->
  Int64.add (Int64.modu (Int64.sub (Int64.repr n) Int64.one) (Int64.repr 64))
    Int64.one = Int64.repr n.
Proof.
  intros Hn. change Int64.one with (Int64.repr 1).
  rewrite cursor_sub by lia. unfold Int64.modu.
  rewrite !cursor_unsigned by lia. rewrite Z.mod_small by lia.
  unfold Int64.add. rewrite !cursor_unsigned by lia. f_equal; lia.
Qed.

Lemma cursor_no_cross n : 8 <= n <= 64 ->
  Int64.ltu (Int64.repr n) (Int64.repr 8) = false.
Proof.
  intros Hn. unfold Int64.ltu. rewrite !cursor_unsigned by lia.
  rewrite zlt_false by lia. reflexivity.
Qed.

(** Concrete word updates performed by increment8's actual helper sequence. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_increment8 C.jet_increment8_exec C.jet_word_bits.
Local Open Scope Z_scope.

Definition increment8_carry_update (old : int64) (r : int) : int64 :=
  if Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)
  then Int64.or old (Int64.repr 256) else clear_low 9 old.

Definition increment8_word_update (old : int64) (r : int) : int64 :=
  put_low 8 (increment8_carry_update old r)
    (Int64.repr (Int.unsigned (increment8_byte r))).

Lemma increment8_word_update_zero r :
  increment8_word_update Int64.zero r = increment8_written_word r.
Proof.
  unfold increment8_word_update, increment8_carry_update, put_low,
    increment8_written_word, increment8_carry_word.
  rewrite Int64.zero_ext_and by lia.
  destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r));
    reflexivity.
Qed.

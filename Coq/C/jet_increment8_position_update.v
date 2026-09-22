(** Exact output updates used by increment at a non-crossing cursor. *)
From Coq Require Import ZArith.
From compcert Require Import Integers.
Require Import C.jet_increment8 C.jet_word_bits C.jet_write8_position.
Local Open Scope Z_scope.

Definition increment8_carry_at (cursor : Z) (old : int64) (r : int) : int64 :=
  if Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)
  then Int64.or old (Int64.shl Int64.one (Int64.repr (cursor - 1)))
  else clear_low cursor old.

Definition increment8_word_at (cursor : Z) (old : int64) (r : int) : int64 :=
  put_byte (cursor - 1) (increment8_carry_at cursor old r)
    (Int64.repr (Int.unsigned (increment8_byte r))).

(** Exact output updates of the C add_8 carry and byte writers. *)
From Coq Require Import ZArith.
From compcert Require Import Integers.
Require Import C.jet_add8 C.jet_word_bits C.jet_write8_position.
Local Open Scope Z_scope.

Definition add8_carry_at (cursor : Z) (old : int64) (r s : int) : int64 :=
  if Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)
  then Int64.or old (Int64.shl Int64.one (Int64.repr (cursor - 1)))
  else clear_low cursor old.

Definition add8_word_at (cursor : Z) (old : int64) (r s : int) : int64 :=
  put_byte (cursor - 1) (add8_carry_at cursor old r s)
    (Int64.repr (Int.unsigned (add8_byte r s))).

(** Scalar facts for the seven possible byte-crossing splits. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import C.jet_word_bits.
Local Open Scope Z_scope.

Definition byte_crossing_arithmetic (k : Z) : Prop :=
  Int64.divu (Int64.sub (Int64.repr (64 + k)) (Int64.repr 1))
    (Int64.repr 64) = Int64.one /\
  Int64.add (Int64.modu (Int64.sub (Int64.repr (64 + k)) (Int64.repr 1))
    (Int64.repr 64)) (Int64.repr 1) = Int64.repr k /\
  Int64.ltu (Int64.repr k) (Int64.repr 8) = true /\
  Int64.sub (Int64.repr 8) (Int64.repr k) = Int64.repr (8 - k) /\
  Int64.sub (Int64.repr (64 + k)) (Int64.repr k) = Int64.repr 64 /\
  Int64.ltu (Int64.repr (8 - k)) (Int64.repr 32) = true /\
  Int.shr Int.one (Int64.loword (Int64.repr (8 - k))) = Int.zero /\
  Int64.sub (Int64.repr 64) (Int64.repr (8 - k)) = Int64.repr (56 + k) /\
  Int64.ltu (Int64.repr (56 + k)) Int64.iwordsize = true /\
  Int64.ltu (Int64.repr 64) (Int64.repr (8 - k)) = false /\
  Int64.zero_ext k Int64.zero = Int64.zero /\
  Int64.zero_ext (8 - k) Int64.one = Int64.one.

Lemma byte_crossing_arithmetic_holds k : 1 <= k <= 7 -> byte_crossing_arithmetic k.
Proof.
  intros HK.
  assert (HC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    unfold byte_crossing_arithmetic; repeat split; reflexivity.
Qed.

Lemma clear_entire_word w : clear_low 64 w = Int64.zero.
Proof.
  apply Int64.same_bits_eq. intros i HI.
  change (0 <= i < 64) in HI.
  rewrite clear_low_bits by lia. rewrite Coqlib.zlt_true by lia.
  symmetry. apply Int64.bits_zero.
Qed.

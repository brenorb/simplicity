(** Shared bridge for the next four-reader multiplication family.
    Word.fullMultiplier is the canonical Programs.Arith.full_multiply term.
    This module is representation infrastructure, not completed C jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Translate.
Require Import C.jet_word_repr C.jet_encoding C.jet_input_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma full_multiply_int64_denotes n (x y z w : Ty.tySem (Word n)) r t u v :
  Z.of_nat (Nat.pow 2 (S n)) <= 64 ->
  Int64.unsigned r = @toZ (WordToZ n) x ->
  Int64.unsigned t = @toZ (WordToZ n) y ->
  Int64.unsigned u = @toZ (WordToZ n) z ->
  Int64.unsigned v = @toZ (WordToZ n) w ->
  @fromZ (WordToZ (S n))
    (Int64.unsigned (Int64.add (Int64.add (Int64.mul r t) u) v)) =
    @fullMultiplier n Alg.CoreFunSem ((x, y), (z, w)).
Proof.
  intros Hwidth Hr Ht Hu Hv.
  pose proof (word_toZ_range (S n) (@fullMultiplier n Alg.CoreFunSem ((x, y), (z, w)))) as Hrange.
  rewrite fullMultiplier_correct in Hrange.
  pose proof (word_toZ_range n z) as Hz.
  pose proof (word_toZ_range n w) as Hw.
  pose proof (word_toZ_range n x) as Hx.
  pose proof (word_toZ_range n y) as Hy.
  assert (Hlimit : 2 ^ Z.of_nat (Nat.pow 2 (S n)) <= Int64.modulus).
  { change Int64.modulus with (2 ^ 64). apply Z.pow_le_mono_r; lia. }
  assert (Hprod : 0 <= @toZ (WordToZ n) x * @toZ (WordToZ n) y).
  { apply Z.mul_nonneg_nonneg; lia. }
  unfold Int64.add, Int64.mul.
  rewrite !Int64.unsigned_repr_eq, Hr, Ht, Hu, Hv.
  rewrite (Z.mod_small (@toZ (WordToZ n) x * @toZ (WordToZ n) y) Int64.modulus) by lia.
  rewrite (Z.mod_small (@toZ (WordToZ n) x * @toZ (WordToZ n) y + @toZ (WordToZ n) z)
    Int64.modulus) by lia.
  rewrite Z.mod_small by lia.
  rewrite <- fullMultiplier_correct. apply from_toZ.
Qed.

Lemma frame_input_word_quad_encode n m bi edge rc (x y z w : Ty.tySem (Word n)) :
  frame_input_cells_at m bi edge rc
    (@encode (Ty.Prod (Ty.Prod (Word n) (Word n)) (Ty.Prod (Word n) (Word n))) ((x, y), (z, w)))
  <->
  frame_input_word_at m bi edge rc x /\
  frame_input_word_at m bi edge (rc + Z.of_nat (Nat.pow 2 n)) y /\
  frame_input_word_at m bi edge (rc + 2 * Z.of_nat (Nat.pow 2 n)) z /\
  frame_input_word_at m bi edge (rc + 3 * Z.of_nat (Nat.pow 2 n)) w.
Proof.
  change (@encode (Ty.Prod (Ty.Prod (Word n) (Word n)) (Ty.Prod (Word n) (Word n)))
    ((x, y), (z, w))) with ((encode x ++ encode y) ++ (encode z ++ encode w)).
  rewrite frame_input_cells_at_app, app_length, !encode_word_length.
  rewrite !frame_input_cells_at_app, !encode_word_length, <- !frame_input_word_at_encode.
  replace (rc + Z.of_nat (Nat.pow 2 n + Nat.pow 2 n))
    with (rc + 2 * Z.of_nat (Nat.pow 2 n)) by lia.
  replace (rc + 2 * Z.of_nat (Nat.pow 2 n) + Z.of_nat (Nat.pow 2 n))
    with (rc + 3 * Z.of_nat (Nat.pow 2 n)) by lia.
  tauto.
Qed.

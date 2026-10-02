(** Canonical right-rotation control bridge, sharing the displacement and
    constant-rotation lemmas with the checked left-rotation family. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_right_rotate_spec C.jet_rotate_word_controls C.jet_word_bit_spec.
Require Import C.jet_word_repr C.jet_wide C.jet_left_rotate_wide_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint right_rotate_low_controls_fun n i count (amount : Ty.tySem (Word 3))
    (x : Ty.tySem (Word n)) : Ty.tySem (Word n) :=
  match count with
  | O => x
  | S count => right_rotate_low_controls_fun n (S i) count amount
      (match @word_bit_spec 3 i Alg.CoreFunSem amount with
       | inl _ => x
       | inr _ => @Word.rotate_const Bit n Alg.CoreFunSem (-(2 ^ Z.of_nat i)) x
       end)
  end.

Lemma right_rotate32_controls_normalform amount (x : Ty.tySem (Word 5)) :
  @right_rotate_word_spec 3 5 Alg.CoreFunSem (amount,x) =
    right_rotate_low_controls_fun 5 0 5 amount x.
Proof.
  destruct amount as [[[a b] [c d]] [[e f] [g h]]].
  destruct c as [[]|[]], d as [[]|[]],
    e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  all: reflexivity.
Qed.

Lemma right_rotate64_controls_normalform amount (x : Ty.tySem (Word 6)) :
  @right_rotate_word_spec 3 6 Alg.CoreFunSem (amount,x) =
    right_rotate_low_controls_fun 6 0 6 amount x.
Proof.
  destruct amount as [[[a b] [c d]] [[e f] [g h]]].
  destruct b as [[]|[]], c as [[]|[]], d as [[]|[]],
    e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  all: reflexivity.
Qed.

Lemma right_rotate_low_controls_bits n i count amount (x : Ty.tySem (Word n)) j :
  0 <= j < two_power_nat n ->
  Z.testbit (@toZ (WordToZ n) (right_rotate_low_controls_fun n i count amount x)) j =
    Z.testbit (@toZ (WordToZ n) x)
      ((j + rotate_control_amount i count amount) mod two_power_nat n).
Proof.
  assert (HN : 0 < two_power_nat n).
  { rewrite two_power_nat_equiv. apply Z.pow_pos_nonneg; lia. }
  revert i x j. induction count as [|count IH]; intros i x j Hj.
  - cbn [right_rotate_low_controls_fun rotate_control_amount].
    rewrite Z.add_0_r, Z.mod_small by exact Hj. reflexivity.
  - cbn [right_rotate_low_controls_fun rotate_control_amount].
    destruct (@word_bit_spec 3 i Alg.CoreFunSem amount) as [u|u].
    + rewrite Z.add_0_l. apply IH; exact Hj.
    + rewrite IH by exact Hj.
      rewrite rotate_const_left_bits by (apply Z.mod_pos_bound; exact HN).
      replace ((j + rotate_control_amount (S i) count amount) mod two_power_nat n - -(2 ^ Z.of_nat i))
        with ((j + rotate_control_amount (S i) count amount) mod two_power_nat n + 2 ^ Z.of_nat i) by lia.
      rewrite Z.add_mod_idemp_l by lia. f_equal. f_equal. lia.
Qed.

Lemma right_rotate_byte_spec_bits s amount x j :
  0 <= j < wide_bits (byte_rotate_width s) ->
  Z.testbit (@toZ (WordToZ (wide_log (byte_rotate_width s)))
    (@right_rotate_byte_spec s Alg.CoreFunSem (amount,x))) j =
  Z.testbit (@toZ (WordToZ (wide_log (byte_rotate_width s))) x)
    ((j + @toZ (WordToZ 3) amount mod wide_bits (byte_rotate_width s)) mod
      wide_bits (byte_rotate_width s)).
Proof.
  intros Hj. destruct s.
  - change (0 <= j < two_power_nat 5) in Hj.
    change (Z.testbit (@toZ (WordToZ 5) (@right_rotate_word_spec 3 5 Alg.CoreFunSem (amount,x))) j =
      Z.testbit (@toZ (WordToZ 5) x) ((j + @toZ (WordToZ 3) amount mod 32) mod 32)).
    rewrite right_rotate32_controls_normalform, right_rotate_low_controls_bits by exact Hj.
    rewrite rotate_control_amount32. reflexivity.
  - change (0 <= j < two_power_nat 6) in Hj.
    change (Z.testbit (@toZ (WordToZ 6) (@right_rotate_word_spec 3 6 Alg.CoreFunSem (amount,x))) j =
      Z.testbit (@toZ (WordToZ 6) x) ((j + @toZ (WordToZ 3) amount mod 64) mod 64)).
    rewrite right_rotate64_controls_normalform, right_rotate_low_controls_bits by exact Hj.
    rewrite rotate_control_amount64. reflexivity.
Qed.

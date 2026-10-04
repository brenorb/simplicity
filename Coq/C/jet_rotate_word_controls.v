(** Symbolic normal form of the literal byte-controlled canonical rotations.
    Only control bits, not payload values or C executions, are case-split. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_rotate_spec C.jet_word_bit_spec C.jet_word_repr.
Require Import C.jet_wide C.jet_left_rotate_wide_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint rotate_low_controls_fun n i count (amount : Ty.tySem (Word 3)) (x : Ty.tySem (Word n)) :
    Ty.tySem (Word n) :=
  match count with
  | O => x
  | S count => rotate_low_controls_fun n (S i) count amount
      (match @word_bit_spec 3 i Alg.CoreFunSem amount with
       | inl _ => x
       | inr _ => @Word.rotate_const Bit n Alg.CoreFunSem (2 ^ Z.of_nat i) x
       end)
  end.

(* This sentence checks 256 finite control cases with a symbolic payload.
   Allow a bounded batch deadline, as for the 64-bit normal form below. *)
Set Default Timeout 30.
Lemma left_rotate32_controls_normalform (amount : Ty.tySem (Word 3)) (x : Ty.tySem (Word 5)) :
  @left_rotate_word_spec 3 5 Alg.CoreFunSem (amount, x) = rotate_low_controls_fun 5 0 5 amount x.
Proof.
  destruct amount as [[[a b] [c d]] [[e f] [g h]]].
  destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
    e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  all: reflexivity.
Qed.

(* The vernacular default bounds the entire 256-case tactic sentence, including
   an explicit inner Timeout. Give just this checked finite-control proof a
   larger bounded deadline; restore the usual short bound immediately below. *)
Set Default Timeout 30.
Lemma left_rotate64_controls_normalform (amount : Ty.tySem (Word 3)) (x : Ty.tySem (Word 6)) :
  @left_rotate_word_spec 3 6 Alg.CoreFunSem (amount, x) = rotate_low_controls_fun 6 0 6 amount x.
Proof.
  destruct amount as [[[a b] [c d]] [[e f] [g h]]].
  destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
    e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  (* This one sentence checks all 256 control cases; retain a bounded batch
     deadline without changing the symbolic-payload proof or its statement. *)
  Timeout 30 all: reflexivity.
Qed.
Set Default Timeout 10.

(** The accumulated displacement is independent of the symbolic payload.
    This interface lets all widths share the same bit-level composition proof. *)
Fixpoint rotate_control_amount i count (amount : Ty.tySem (Word 3)) : Z :=
  match count with
  | O => 0
  | S count =>
      (match @word_bit_spec 3 i Alg.CoreFunSem amount with
       | inl _ => 0
       | inr _ => 2 ^ Z.of_nat i
       end) + rotate_control_amount (S i) count amount
  end.

Lemma rotate_const_left_bits n a (x : Ty.tySem (Word n)) j :
  0 <= j < two_power_nat n ->
  Z.testbit (@toZ (WordToZ n) (@Word.rotate_const Bit n Alg.CoreFunSem a x)) j =
    Z.testbit (@toZ (WordToZ n) x) ((j - a) mod two_power_nat n).
Proof.
  intros Hj. pose proof (@Word.rotate_const_correct_word n (-a) x j Hj) as H.
  rewrite Z.opp_involutive in H. replace (j + -a) with (j - a) in H by lia. exact H.
Qed.

Lemma rotate_mod_sub a b modulus : modulus <> 0 ->
  ((a mod modulus - b) mod modulus) = ((a - b) mod modulus).
Proof.
  intros H. replace (a mod modulus - b) with (a mod modulus + -b) by lia.
  rewrite Z.add_mod_idemp_l by exact H. reflexivity.
Qed.

Lemma rotate_low_controls_bits n i count amount (x : Ty.tySem (Word n)) j :
  0 <= j < two_power_nat n ->
  Z.testbit (@toZ (WordToZ n) (rotate_low_controls_fun n i count amount x)) j =
    Z.testbit (@toZ (WordToZ n) x)
      ((j - rotate_control_amount i count amount) mod two_power_nat n).
Proof.
  assert (HN : 0 < two_power_nat n).
  { rewrite two_power_nat_equiv. apply Z.pow_pos_nonneg; lia. }
  revert i x j. induction count as [|count IH]; intros i x j Hj.
  - cbn [rotate_low_controls_fun rotate_control_amount].
    rewrite Z.sub_0_r, Z.mod_small by exact Hj. reflexivity.
  - cbn [rotate_low_controls_fun rotate_control_amount].
    destruct (@word_bit_spec 3 i Alg.CoreFunSem amount) as [u|u].
    + rewrite Z.add_0_l. apply IH; exact Hj.
    + rewrite IH by exact Hj.
      rewrite rotate_const_left_bits by (apply Z.mod_pos_bound; exact HN).
      rewrite rotate_mod_sub by lia. f_equal. f_equal. lia.
Qed.

Lemma rotate_control_amount32 amount :
  rotate_control_amount 0 5 amount = @toZ (WordToZ 3) amount mod 32.
Proof.
  destruct amount as [[[a b] [c d]] [[e f] [g h]]].
  destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
    e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  all: reflexivity.
Qed.

Lemma rotate_control_amount64 amount :
  rotate_control_amount 0 6 amount = @toZ (WordToZ 3) amount mod 64.
Proof.
  destruct amount as [[[a b] [c d]] [[e f] [g h]]].
  destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
    e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  all: reflexivity.
Qed.

Lemma left_rotate_byte_spec_bits s amount x j :
  0 <= j < wide_bits (byte_rotate_width s) ->
  Z.testbit (@toZ (WordToZ (wide_log (byte_rotate_width s)))
    (@left_rotate_byte_spec s Alg.CoreFunSem (amount,x))) j =
  Z.testbit (@toZ (WordToZ (wide_log (byte_rotate_width s))) x)
    ((j - @toZ (WordToZ 3) amount mod wide_bits (byte_rotate_width s)) mod
      wide_bits (byte_rotate_width s)).
Proof.
  intros Hj. destruct s.
  - change (0 <= j < two_power_nat 5) in Hj.
    change (Z.testbit (@toZ (WordToZ 5) (@left_rotate_word_spec 3 5 Alg.CoreFunSem (amount,x))) j =
      Z.testbit (@toZ (WordToZ 5) x) ((j - @toZ (WordToZ 3) amount mod 32) mod 32)).
    rewrite left_rotate32_controls_normalform, rotate_low_controls_bits by exact Hj.
    rewrite rotate_control_amount32. reflexivity.
  - change (0 <= j < two_power_nat 6) in Hj.
    change (Z.testbit (@toZ (WordToZ 6) (@left_rotate_word_spec 3 6 Alg.CoreFunSem (amount,x))) j =
      Z.testbit (@toZ (WordToZ 6) x) ((j - @toZ (WordToZ 3) amount mod 64) mod 64)).
    rewrite left_rotate64_controls_normalform, rotate_low_controls_bits by exact Hj.
    rewrite rotate_control_amount64. reflexivity.
Qed.

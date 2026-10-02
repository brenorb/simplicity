(** Width-generic control normal form shared by left and right rotations.
    Canonical-program adapters are separate; this is not jet coverage. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec C.jet_word_repr C.jet_rotate_word_controls.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate_signed_amount (right : bool) amount := if right then -amount else amount.
Fixpoint rotate_control_word_fun m n right i count (amount : Ty.tySem (Word m))
    (x : Ty.tySem (Word n)) : Ty.tySem (Word n) :=
  match count with
  | O => x
  | S count => rotate_control_word_fun m n right (S i) count amount
      (match @word_bit_spec m i Alg.CoreFunSem amount with
       | inl _ => x
       | inr _ => @Word.rotate_const Bit n Alg.CoreFunSem
           (rotate_signed_amount right (2 ^ Z.of_nat i)) x
       end)
  end.
Fixpoint rotate_control_word_amount m i count (amount : Ty.tySem (Word m)) : Z :=
  match count with
  | O => 0
  | S count =>
      (match @word_bit_spec m i Alg.CoreFunSem amount with
       | inl _ => 0 | inr _ => 2 ^ Z.of_nat i
       end) + rotate_control_word_amount m (S i) count amount
  end.

Lemma rotate_control_word_bits m n right i count amount (x : Ty.tySem (Word n)) j :
  0 <= j < two_power_nat n ->
  Z.testbit (@toZ (WordToZ n) (rotate_control_word_fun m n right i count amount x)) j =
    Z.testbit (@toZ (WordToZ n) x)
      ((j - rotate_signed_amount right (rotate_control_word_amount m i count amount)) mod two_power_nat n).
Proof.
  assert (HN : 0 < two_power_nat n).
  { rewrite two_power_nat_equiv. apply Z.pow_pos_nonneg; lia. }
  revert i x j. induction count as [|count IH]; intros i x j Hj.
  - cbn [rotate_control_word_fun rotate_control_word_amount].
    replace (rotate_signed_amount right 0) with 0 by (destruct right; reflexivity).
    rewrite Z.sub_0_r, Z.mod_small by exact Hj. reflexivity.
  - cbn [rotate_control_word_fun rotate_control_word_amount].
    destruct (@word_bit_spec m i Alg.CoreFunSem amount) as [u|u].
    + rewrite Z.add_0_l. apply IH; exact Hj.
    + rewrite IH by exact Hj.
      rewrite rotate_const_left_bits by (apply Z.mod_pos_bound; exact HN).
      rewrite rotate_mod_sub by lia. f_equal. f_equal. destruct right; cbn [rotate_signed_amount]; lia.
Qed.

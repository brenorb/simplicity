(** Symbolic low-bit bridge for the actual byte helper. In particular the
    promoted C right shift remains Int.shr, not an assumed Int.shru rewrite. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_word_repr C.jet_rotate8_helper.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma rotate8_result_bits (x : Ty.tySem (Word 3)) r a j :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  0 <= Int.unsigned a < 8 -> 0 <= j < 8 ->
  Int.testbit (rotate8_result r a) j =
    Z.testbit (@toZ (WordToZ 3) x) ((j - Int.unsigned a) mod 8).
Proof.
  intros Hr HA Hj. unfold rotate8_result. pose proof (Int.eq_spec a Int.zero) as HZ.
  destruct (Int.eq a Int.zero) eqn:HZb.
  - subst a. rewrite Int.unsigned_zero, Z.sub_0_r, Z.mod_small by exact Hj.
    unfold Int.testbit. rewrite Hr. reflexivity.
  - assert (HP : 0 < Int.unsigned a).
    { assert (Int.unsigned a <> 0).
      { intro HE. apply HZ. rewrite <- (Int.repr_unsigned a), HE. reflexivity. } lia. }
    assert (HR : Int.unsigned (Int.repr (8 - Int.unsigned a)) = 8 - Int.unsigned a).
    { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
    unfold rotate8_nonzero.
    rewrite Int.bits_zero_ext, (zlt_true _ j 8) by lia.
    rewrite Int.bits_or, Int.bits_shl, Int.bits_shr by (change Int.zwordsize with 32; lia).
    rewrite HR. change Int.zwordsize with 32.
    rewrite (zlt_true _ (j + (8 - Int.unsigned a)) 32) by lia.
    destruct (zlt j (Int.unsigned a)) as [Hlt|Hge].
    + cbn [orb].
      assert (HM : (j - Int.unsigned a) mod 8 = j + 8 - Int.unsigned a).
      { symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
      rewrite HM. unfold Int.testbit. rewrite Hr. f_equal; lia.
    + assert (HB : Int.testbit r (j + (8 - Int.unsigned a)) = false).
      { unfold Int.testbit. rewrite Hr. apply word_toZ_high_bits. change (8 <= j + (8 - Int.unsigned a)); lia. }
      rewrite HB, orb_false_r, Z.mod_small by lia.
      unfold Int.testbit. rewrite Hr. reflexivity.
Qed.

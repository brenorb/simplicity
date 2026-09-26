(** Symbolic bridge from the C add_32 arithmetic to Simplicity's adder. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec.
Require Import C.jet_increment_wide_word C.jet_read32_input_word.
Local Open Scope Z_scope.

Definition add32_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word 5) (Word 5))
      (Ty.Prod Bit (Word 5)) := @Word.adder 5 term.

Definition add32_spec_value :
    Ty.tySem (Ty.Prod (Word 5) (Word 5)) ->
      Ty.tySem (Ty.Prod Bit (Word 5)) := @add32_spec Alg.CoreFunSem.

Definition add32_carry (x y : int64) : bool :=
  Int64.ltu (Int64.sub (Int64.repr 4294967295) y) x.

Definition add32_payload (x y : int64) : int64 := Int64.add x y.

Lemma add32_carry_denotes_overflow x y :
  Int64.unsigned x <= 4294967295 -> Int64.unsigned y <= 4294967295 ->
  add32_carry x y = (4294967295 <? Int64.unsigned x + Int64.unsigned y).
Proof.
  intros Hx Hy. unfold add32_carry, Int64.ltu.
  assert (Hsub : Int64.unsigned (Int64.sub (Int64.repr 4294967295) y) =
      4294967295 - Int64.unsigned y).
  { rewrite Int64.unsigned_sub_borrow.
    unfold Int64.sub_borrow.
    rewrite Int64.unsigned_repr by
      (change (0 <= 4294967295 <= 18446744073709551615); lia).
    rewrite Int64.unsigned_zero.
    rewrite zlt_false by lia. rewrite Int64.unsigned_zero. lia. }
  rewrite Hsub.
  destruct (zlt (4294967295 - Int64.unsigned y) (Int64.unsigned x));
    destruct (zlt 4294967295 (Int64.unsigned x + Int64.unsigned y));
    simpl; try reflexivity; lia.
Qed.

Lemma add32_values_denote_input r s (x y : Ty.tySem (Word 5)) :
  Int64.unsigned r = @toZ (WordToZ 5) x ->
  Int64.unsigned s = @toZ (WordToZ 5) y ->
  ((if add32_carry r s then inr tt else inl tt),
    decode_wide W32 (Int64.zero_ext 32 (add32_payload r s))) =
  add32_spec_value (x, y).
Proof.
  intros Hr Hs.
  assert (Hrle : Int64.unsigned r <= 4294967295).
  { rewrite Hr. pose proof (word32_toZ_range x); lia. }
  assert (Hsle : Int64.unsigned s <= 4294967295).
  { rewrite Hs. pose proof (word32_toZ_range y); lia. }
  pose proof (Int64.unsigned_range r) as Hru.
  pose proof (Int64.unsigned_range s) as Hsu.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 5))).
  unfold add32_spec_value, add32_spec.
  rewrite Word.adder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 5)).
  unfold decode_wide, add32_payload.
  rewrite to_fromZ.
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  unfold Int64.add.
  rewrite Int64.unsigned_repr by
    (change (0 <= Int64.unsigned r + Int64.unsigned s <= 18446744073709551615); lia).
  rewrite add32_carry_denotes_overflow by assumption.
  rewrite !Hr, !Hs.
  pose proof (word32_toZ_range x) as Hx.
  pose proof (word32_toZ_range y) as Hy.
  change (@toZ BitToZ
      (if 4294967295 <? @toZ (WordToZ 5) x + @toZ (WordToZ 5) y
       then inr tt else inl tt) * 4294967296 +
      ((@toZ (WordToZ 5) x + @toZ (WordToZ 5) y) mod 4294967296) mod 4294967296 =
    @toZ (WordToZ 5) x + @toZ (WordToZ 5) y).
  rewrite Z.mod_mod by lia.
  destruct (4294967295 <? @toZ (WordToZ 5) x + @toZ (WordToZ 5) y)
    eqn:Hcarry.
  - apply Z.ltb_lt in Hcarry.
    change (1 * 4294967296 +
      (@toZ (WordToZ 5) x + @toZ (WordToZ 5) y) mod 4294967296 =
        @toZ (WordToZ 5) x + @toZ (WordToZ 5) y).
    replace ((@toZ (WordToZ 5) x + @toZ (WordToZ 5) y) mod 4294967296)
      with (@toZ (WordToZ 5) x + @toZ (WordToZ 5) y - 4294967296).
    + lia.
    + apply Z.mod_unique with 1; pose proof (word32_toZ_range x);
        pose proof (word32_toZ_range y); lia.
  - apply Z.ltb_ge in Hcarry.
    change (0 * 4294967296 +
      (@toZ (WordToZ 5) x + @toZ (WordToZ 5) y) mod 4294967296 =
        @toZ (WordToZ 5) x + @toZ (WordToZ 5) y).
    rewrite Z.mod_small; [lia|].
    pose proof (word32_toZ_range x). pose proof (word32_toZ_range y). lia.
Qed.

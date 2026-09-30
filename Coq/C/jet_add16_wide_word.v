(** Symbolic bridge from the C add_16 arithmetic to Simplicity's adder. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec.
Require Import C.jet_increment_wide_word.
Require Import C.jet_read16_input_word.
Require Export C.jet_toZ.
Local Open Scope Z_scope.

Definition add16_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word 4) (Word 4))
      (Ty.Prod Bit (Word 4)) := @Word.adder 4 term.

Definition add16_spec_value :
    Ty.tySem (Ty.Prod (Word 4) (Word 4)) ->
      Ty.tySem (Ty.Prod Bit (Word 4)) := @add16_spec Alg.CoreFunSem.

Definition add16_carry (x y : int64) : bool :=
  Int64.ltu (Int64.sub (Int64.repr 65535) y) x.

Definition add16_payload (x y : int64) : int64 := Int64.add x y.

Lemma add16_carry_denotes_overflow x y :
  Int64.unsigned x <= 65535 -> Int64.unsigned y <= 65535 ->
  add16_carry x y = (65535 <? Int64.unsigned x + Int64.unsigned y).
Proof.
  intros Hx Hy. unfold add16_carry, Int64.ltu.
  assert (Hsub : Int64.unsigned (Int64.sub (Int64.repr 65535) y) =
      65535 - Int64.unsigned y).
  { rewrite Int64.unsigned_sub_borrow.
    unfold Int64.sub_borrow.
    rewrite Int64.unsigned_repr by
      (change (0 <= 65535 <= 18446744073709551615); lia).
    rewrite Int64.unsigned_zero.
    rewrite zlt_false by lia. rewrite Int64.unsigned_zero. lia. }
  rewrite Hsub.
  destruct (zlt (65535 - Int64.unsigned y) (Int64.unsigned x));
    destruct (zlt 65535 (Int64.unsigned x + Int64.unsigned y));
    simpl; try reflexivity; lia.
Qed.

Lemma add16_values_denote_input r s (x y : Ty.tySem (Word 4)) :
  Int64.unsigned r = @toZ (WordToZ 4) x ->
  Int64.unsigned s = @toZ (WordToZ 4) y ->
  ((if add16_carry r s then inr tt else inl tt),
    decode_wide W16 (Int64.zero_ext 16 (add16_payload r s))) =
  add16_spec_value (x, y).
Proof.
  intros Hr Hs.
  assert (Hrle : Int64.unsigned r <= 65535).
  { rewrite Hr. pose proof (word16_toZ_range x); lia. }
  assert (Hsle : Int64.unsigned s <= 65535).
  { rewrite Hs. pose proof (word16_toZ_range y); lia. }
  pose proof (Int64.unsigned_range r) as Hru.
  pose proof (Int64.unsigned_range s) as Hsu.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 4))).
  unfold add16_spec_value, add16_spec.
  rewrite Word.adder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 4)).
  unfold decode_wide, add16_payload.
  rewrite to_fromZ.
  rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
  unfold Int64.add.
  rewrite Int64.unsigned_repr by
    (change (0 <= Int64.unsigned r + Int64.unsigned s <= 18446744073709551615); lia).
  rewrite add16_carry_denotes_overflow by assumption.
  rewrite !Hr, !Hs.
  pose proof (word16_toZ_range x) as Hx.
  pose proof (word16_toZ_range y) as Hy.
  change (@toZ BitToZ
      (if 65535 <? @toZ (WordToZ 4) x + @toZ (WordToZ 4) y
       then inr tt else inl tt) * 65536 +
      ((@toZ (WordToZ 4) x + @toZ (WordToZ 4) y) mod 65536) mod 65536 =
    @toZ (WordToZ 4) x + @toZ (WordToZ 4) y).
  rewrite Z.mod_mod by lia.
  destruct (65535 <? @toZ (WordToZ 4) x + @toZ (WordToZ 4) y) eqn:Hcarry.
  - apply Z.ltb_lt in Hcarry.
    change (1 * 65536 +
      (@toZ (WordToZ 4) x + @toZ (WordToZ 4) y) mod 65536 =
        @toZ (WordToZ 4) x + @toZ (WordToZ 4) y).
    replace ((@toZ (WordToZ 4) x + @toZ (WordToZ 4) y) mod 65536)
      with (@toZ (WordToZ 4) x + @toZ (WordToZ 4) y - 65536).
    + lia.
    + apply Z.mod_unique with 1; pose proof (word16_toZ_range x);
        pose proof (word16_toZ_range y); lia.
  - apply Z.ltb_ge in Hcarry.
    change (0 * 65536 +
      (@toZ (WordToZ 4) x + @toZ (WordToZ 4) y) mod 65536 =
        @toZ (WordToZ 4) x + @toZ (WordToZ 4) y).
    rewrite Z.mod_small; [lia|].
    pose proof (word16_toZ_range x). pose proof (word16_toZ_range y). lia.
Qed.

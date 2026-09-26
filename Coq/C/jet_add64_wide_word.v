(** Symbolic arithmetic bridge from C add_64 to Simplicity's 64-bit adder. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec C.jet_read64_input_word.
Require Import C.jet_increment_wide_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition add64_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word 6) (Word 6))
      (Ty.Prod Bit (Word 6)) := @Word.adder 6 term.

Definition add64_spec_value :
    Ty.tySem (Ty.Prod (Word 6) (Word 6)) -> Ty.tySem (Ty.Prod Bit (Word 6)) :=
  @add64_spec Alg.CoreFunSem.

Definition add64_carry (x y : int64) : bool :=
  Int64.ltu (Int64.sub Int64.mone y) x.

Definition add64_payload (x y : int64) : int64 := Int64.add x y.

Lemma add64_carry_denotes_overflow x y :
  add64_carry x y =
    (18446744073709551615 <? Int64.unsigned x + Int64.unsigned y).
Proof.
  unfold add64_carry, Int64.ltu.
  assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (Hsub : Int64.unsigned (Int64.sub Int64.mone y) =
      18446744073709551615 - Int64.unsigned y).
  { rewrite Int64.unsigned_sub_borrow.
    unfold Int64.sub_borrow.
    assert (Hmodulus : Int64.modulus = 18446744073709551616) by reflexivity.
    rewrite Int64.unsigned_mone, Int64.unsigned_zero.
    rewrite Hmodulus.
    rewrite zlt_false by (pose proof (Int64.unsigned_range y); lia).
    rewrite Int64.unsigned_zero. lia. }
  rewrite Hsub.
  pose proof (Int64.unsigned_range_2 x) as Hx.
  pose proof (Int64.unsigned_range_2 y) as Hy.
  rewrite HM in Hx, Hy.
  destruct (zlt (18446744073709551615 - Int64.unsigned y)
      (Int64.unsigned x)) as [Hcut|Hcut].
  - destruct (18446744073709551615 <? Int64.unsigned x + Int64.unsigned y)
      eqn:Hcarry.
    + reflexivity.
    + apply Z.ltb_ge in Hcarry. lia.
  - destruct (18446744073709551615 <? Int64.unsigned x + Int64.unsigned y)
      eqn:Hcarry.
    + apply Z.ltb_lt in Hcarry. lia.
    + reflexivity.
Qed.

Lemma add64_values_denote_input r s (x y : Ty.tySem (Word 6)) :
  Int64.unsigned r = @toZ (WordToZ 6) x ->
  Int64.unsigned s = @toZ (WordToZ 6) y ->
  ((if add64_carry r s then inr tt else inl tt),
    decode_wide W64 (Int64.zero_ext 64 (add64_payload r s))) =
  add64_spec_value (x, y).
Proof.
  intros Hr Hs.
  pose proof (Int64.unsigned_range r) as Hru.
  pose proof (Int64.unsigned_range s) as Hsu.
  pose proof (Int64.unsigned_add_either r s) as Hadd.
  assert (HM : Int64.modulus = 18446744073709551616) by reflexivity.
  assert (Hmax : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (Hmodr : @toZ (WordToZ 6) x =
      Z.modulo (@toZ (WordToZ 6) x) 18446744073709551616).
  { pose proof (@toZ_mod (WordToZ 6) x) as H.
    rewrite two_power_nat_equiv in H. rewrite (bitSize_Word 6) in H.
    change (@toZ (WordToZ 6) x =
      Z.modulo (@toZ (WordToZ 6) x) 18446744073709551616) in H.
    exact H. }
  assert (Hmody : @toZ (WordToZ 6) y =
      Z.modulo (@toZ (WordToZ 6) y) 18446744073709551616).
  { pose proof (@toZ_mod (WordToZ 6) y) as H.
    rewrite two_power_nat_equiv in H. rewrite (bitSize_Word 6) in H.
    change (@toZ (WordToZ 6) y =
      Z.modulo (@toZ (WordToZ 6) y) 18446744073709551616) in H.
    exact H. }
  apply (toZ_injective (PairToZ BitToZ (WordToZ 6))).
  unfold add64_spec_value, add64_spec.
  rewrite Word.adder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 6)).
  unfold add64_payload, decode_wide.
  rewrite Int64.zero_ext_above by (assert (Hws : Int64.zwordsize = 64) by reflexivity; rewrite Hws; lia).
  rewrite !to_fromZ.
  rewrite <- Hr, <- Hs.
  assert (Hpow : two_power_nat (bitSize (WordToZ 6)) = 18446744073709551616)
    by reflexivity.
  rewrite Hpow.
  destruct Hadd as [Hsum|Hwrap].
  - rewrite Hsum.
    assert (Hsumlt : Int64.unsigned r + Int64.unsigned s <
        18446744073709551616).
    { pose proof (Int64.unsigned_range (Int64.add r s)) as Hout.
      rewrite Hsum, HM in Hout. exact (proj2 Hout). }
    assert (Hcarry : add64_carry r s = Datatypes.false).
    { rewrite add64_carry_denotes_overflow. apply Z.ltb_ge.
      pose proof (Int64.unsigned_range_2 r) as Hrr.
      pose proof (Int64.unsigned_range_2 s) as Hss.
      pose proof (Int64.unsigned_range (Int64.add r s)) as Hout.
      rewrite Hsum, HM in Hout. rewrite Hmax in Hrr, Hss. lia. }
    rewrite Hcarry. cbn. rewrite (Z.mod_small
      (Int64.unsigned r + Int64.unsigned s) 18446744073709551616)
      by (split; [lia|exact Hsumlt]).
    lia.
  - rewrite HM in Hwrap. rewrite Hwrap.
    assert (Hwraprange : 0 <= Int64.unsigned r + Int64.unsigned s -
        18446744073709551616 < 18446744073709551616).
    { pose proof (Int64.unsigned_range (Int64.add r s)) as Hout.
      rewrite Hwrap, HM in Hout. exact Hout. }
    assert (Hcarry : add64_carry r s = Datatypes.true).
    { rewrite add64_carry_denotes_overflow. apply Z.ltb_lt.
      pose proof (Int64.unsigned_range_2 r) as Hrr.
      pose proof (Int64.unsigned_range_2 s) as Hss.
      pose proof (Int64.unsigned_range (Int64.add r s)) as Hout.
      rewrite Hwrap, HM in Hout. rewrite Hmax in Hrr, Hss. lia. }
    rewrite Hcarry.
    change (@toZ BitToZ Bit.one * 18446744073709551616 +
      ((Int64.unsigned r + Int64.unsigned s - 18446744073709551616) mod
        18446744073709551616) =
      Int64.unsigned r + Int64.unsigned s).
    rewrite Z.mod_small by exact Hwraprange.
    assert (Hbitone : @toZ BitToZ Bit.one = 1) by reflexivity.
    rewrite Hbitone.
    lia.
Qed.

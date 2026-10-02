(** Representation bridge to the literal CoreJets.DivMod128_64 program:
    div2n1n_word_spec 6. These bridges alone are not C jet coverage. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_order_spec C.jet_division_core_spec.
Require Import C.jet_division_result_spec C.jet_division_correction_spec.
Require Import C.jet_divmod96_value.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod128_input_value (xh : Ty.tySem (Word 6)) (xm xl : Ty.tySem (Word 5)) ah am al :
  Int64.unsigned ah = @toZ (WordToZ 6) xh ->
  Int64.unsigned am = @toZ (WordToZ 5) xm ->
  Int64.unsigned al = @toZ (WordToZ 5) xl ->
  @toZ (WordToZ 7) (xh,(xm,xl)) =
    (Int64.unsigned ah * divmod96_radix + Int64.unsigned am) * divmod96_radix + Int64.unsigned al.
Proof.
  intros HH HM HL. rewrite HH, HM, HL.
  change (@toZ (WordToZ 6) xh * 18446744073709551616 +
    (@toZ (WordToZ 5) xm * 4294967296 + @toZ (WordToZ 5) xl) =
    (@toZ (WordToZ 6) xh * 4294967296 + @toZ (WordToZ 5) xm) * 4294967296 + @toZ (WordToZ 5) xl).
  ring.
Qed.

Lemma divmod128_valid_representation (a : Ty.tySem (Word 7)) (b : Ty.tySem (Word 6)) qh ql rf :
  word_modulus 6 <= 2 * @toZ (WordToZ 6) b ->
  @toZ (WordToZ 7) a < @toZ (WordToZ 6) b * word_modulus 6 ->
  0 <= Int64.unsigned qh < divmod96_radix -> 0 <= Int64.unsigned ql < divmod96_radix ->
  0 <= Int64.unsigned rf < @toZ (WordToZ 6) b ->
  @toZ (WordToZ 7) a =
    (Int64.unsigned qh * divmod96_radix + Int64.unsigned ql) * @toZ (WordToZ 6) b + Int64.unsigned rf ->
  ((@fromZ (WordToZ 5) (Int64.unsigned qh), @fromZ (WordToZ 5) (Int64.unsigned ql)),
    @fromZ (WordToZ 6) (Int64.unsigned rf)) = @div2n1n_word_spec 6 Alg.CoreFunSem (a,b).
Proof.
  intros Hnorm Hbound Hqh Hql Hrf Hbalance.
  destruct (div2n1n_normalized_observation 6 a b Hnorm Hbound) as [HQ HR].
  destruct (division_euclidean_observation (@toZ (WordToZ 7) a) (@toZ (WordToZ 6) b)
    (Int64.unsigned qh * divmod96_radix + Int64.unsigned ql) (Int64.unsigned rf)
    ltac:(symmetry; exact Hbalance) Hrf) as [Hqc Hrc].
  destruct (@div2n1n_word_spec 6 Alg.CoreFunSem (a,b)) as [q r] eqn:Hqr.
  cbn [fst snd] in HQ, HR. apply f_equal2.
  - apply (toZ_injective (WordToZ 6)).
    change (@toZ (WordToZ 5) (@fromZ (WordToZ 5) (Int64.unsigned qh)) * divmod96_radix +
      @toZ (WordToZ 5) (@fromZ (WordToZ 5) (Int64.unsigned ql)) = @toZ (WordToZ 6) q).
    rewrite !to_fromZ.
    change ((Int64.unsigned qh mod divmod96_radix) * divmod96_radix +
      (Int64.unsigned ql mod divmod96_radix) = @toZ (WordToZ 6) q).
    rewrite !Z.mod_small by assumption. rewrite HQ. exact Hqc.
  - apply (toZ_injective (WordToZ 6)). rewrite to_fromZ.
    change (Int64.unsigned rf mod Int64.modulus = @toZ (WordToZ 6) r).
    rewrite Z.mod_small by apply Int64.unsigned_range. rewrite HR. exact Hrc.
Qed.

Definition divmod128_guard ah b :=
  andb (negb (Int64.ltu b (Int64.repr 9223372036854775808))) (Int64.ltu ah b).

Lemma divmod128_conditions_match (xh : Ty.tySem (Word 6)) (xm xl : Ty.tySem (Word 5))
    (y : Ty.tySem (Word 6)) ah am al b :
  Int64.unsigned ah = @toZ (WordToZ 6) xh ->
  Int64.unsigned am = @toZ (WordToZ 5) xm -> Int64.unsigned al = @toZ (WordToZ 5) xl ->
  Int64.unsigned b = @toZ (WordToZ 6) y ->
  Bit.toBool (@div2n1n_conditions 6 Alg.CoreFunSem ((xh,(xm,xl)),y)) = divmod128_guard ah b.
Proof.
  intros HH HM HL HB. unfold divmod128_guard.
  assert (HN : negb (Int64.ltu b (Int64.repr 9223372036854775808)) =
      negb (2 * @toZ (WordToZ 6) y <? word_modulus 6)).
  { unfold Int64.ltu. change (Int64.unsigned (Int64.repr 9223372036854775808)) with 9223372036854775808.
    rewrite HB. destruct (zlt (@toZ (WordToZ 6) y) 9223372036854775808) as [Hlt|Hge]; cbn [negb].
    - assert (HT : (2 * @toZ (WordToZ 6) y <? word_modulus 6) = Datatypes.true).
      { apply Z.ltb_lt. change (word_modulus 6) with 18446744073709551616. lia. }
      rewrite HT. reflexivity.
    - assert (HT : (2 * @toZ (WordToZ 6) y <? word_modulus 6) = Datatypes.false).
      { apply Z.ltb_ge. change (word_modulus 6) with 18446744073709551616. lia. }
      rewrite HT. reflexivity. }
  rewrite HN. rewrite div2n1n_conditions_observation, <- division_high_less.
  rewrite lt_word_spec_numeric.
  unfold Int64.ltu. rewrite HH, HB.
  destruct (zlt (@toZ (WordToZ 6) xh) (@toZ (WordToZ 6) y));
    f_equal; [apply Z.ltb_lt|apply Z.ltb_ge]; cbn [fst]; lia.
Qed.

Lemma divmod128_invalid_representation (a : Ty.tySem (Word 7)) (b : Ty.tySem (Word 6)) :
  Bit.toBool (@div2n1n_conditions 6 Alg.CoreFunSem (a,b)) = Datatypes.false ->
  (@fromZ (WordToZ 6) Int64.max_unsigned, @fromZ (WordToZ 6) Int64.max_unsigned) =
    @div2n1n_word_spec 6 Alg.CoreFunSem (a,b).
Proof.
  intros HG. assert (Hz : @div2n1n_conditions 6 Alg.CoreFunSem (a,b) = Bit.zero).
  { destruct (@div2n1n_conditions 6 Alg.CoreFunSem (a,b)) as [[]|[]]; [reflexivity|discriminate]. }
  rewrite div2n1n_invalid_result by exact Hz.
  apply (toZ_injective (WordToZ 7)). rewrite division_high_word_value.
  change (@toZ (WordToZ 6) (@fromZ (WordToZ 6) Int64.max_unsigned) * word_modulus 6 +
    @toZ (WordToZ 6) (@fromZ (WordToZ 6) Int64.max_unsigned) = word_modulus 7 - 1).
  rewrite !to_fromZ. reflexivity.
Qed.

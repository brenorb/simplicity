(** Literal quotient approximation for Programs.Arith.div3n2n.
    The recursive hypothesis is about the actual smaller canonical call. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_division_core_spec C.jet_division_correction_spec.
Require Import C.jet_predicate_spec C.jet_order_spec C.jet_test_value_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma division_leading_normalized n (hi lo : Ty.tySem (Word n)) :
  word_modulus (S n) <= 2 * @toZ (WordToZ (S n)) (hi,lo) ->
  word_modulus n <= 2 * @toZ (WordToZ n) hi.
Proof.
  intros Hnorm.
  change (word_modulus (S n) <=
    2 * (@toZ (WordToZ n) hi * word_modulus n + @toZ (WordToZ n) lo)) in Hnorm.
  rewrite word_modulus_S in Hnorm.
  pose proof (word_value_bounds n lo) as HL.
  destruct (division_word_modulus_even n) as [k [HK HE]].
  rewrite HE in Hnorm, HL |- *. nia.
Qed.

Lemma division_leading_not_greater n (a1 a2 a3 b1 b2 : Ty.tySem (Word n)) :
  (@toZ (WordToZ n) a1 * word_modulus n + @toZ (WordToZ n) a2) * word_modulus n +
    @toZ (WordToZ n) a3 < @toZ (WordToZ (S n)) (b1,b2) * word_modulus n ->
  @toZ (WordToZ n) a1 <= @toZ (WordToZ n) b1.
Proof.
  intros HN.
  change ((@toZ (WordToZ n) a1 * word_modulus n + @toZ (WordToZ n) a2) * word_modulus n +
    @toZ (WordToZ n) a3 <
    (@toZ (WordToZ n) b1 * word_modulus n + @toZ (WordToZ n) b2) * word_modulus n) in HN.
  pose proof (word_modulus_positive n) as HM.
  pose proof (word_value_bounds n a2) as HA2.
  pose proof (word_value_bounds n a3) as HA3.
  pose proof (word_value_bounds n b2) as HB2. nia.
Qed.

Lemma div3n2n_approx_unfold n
    (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n)))
    (a1 a2 b1 : Ty.tySem (Word n)) :
  @div3n2n_approx_spec n Alg.CoreFunSem rec ((a1,a2),b1) =
  match @lt_word_spec Alg.CoreFunSem n (a1,b1) with
  | inl _ => let s := @Word.adder n Alg.CoreFunSem (a2,b1) in
    (fst s,(@division_high_word n Alg.CoreFunSem tt,snd s))
  | inr _ => (Bit.zero,rec ((a1,a2),b1))
  end.
Proof. reflexivity. Qed.

Lemma division_approx_residual_bounds B A N D a3 b1 b2 q r :
  2 <= B -> 0 <= a3 < B -> 0 <= b1 < B -> 0 <= b2 < B ->
  B*B <= 2*D -> D = b1*B+b2 -> N = A*B+a3 -> N < D*B ->
  0 <= q < B -> 0 <= r -> A = q*b1+r ->
  (r < b1 \/ q = B-1) ->
  -2*D <= N-q*D < D.
Proof.
  intros HB HA3 HB1 HB2 Hnorm HD HN Hbound HQ HR HA Hcase.
  assert (Hres : N-q*D = r*B+a3-q*b2) by (rewrite HN, HD, HA; ring).
  assert (Hprod : 0 <= q*b2 <= (B-1)*(B-1)) by nia.
  assert (Hsquare : (B-1)*(B-1) < B*B) by nia.
  assert (Hlower : -(B*B) < N-q*D) by (rewrite Hres; nia).
  split; [lia|].
  destruct Hcase as [Hstrict|Hequal].
  - rewrite Hres. nia.
  - rewrite Hequal. nia.
Qed.

Definition division_normalized_result n
    (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) : Prop :=
  forall (a : Ty.tySem (Word (S n))) (b : Ty.tySem (Word n)),
  word_modulus n <= 2 * @toZ (WordToZ n) b ->
  @toZ (WordToZ (S n)) a < @toZ (WordToZ n) b * word_modulus n ->
  let qr := rec (a,b) in
  @toZ (WordToZ n) (fst qr) * @toZ (WordToZ n) b + @toZ (WordToZ n) (snd qr) =
    @toZ (WordToZ (S n)) a /\
  0 <= @toZ (WordToZ n) (snd qr) < @toZ (WordToZ n) b.

Lemma div3n2n_approx_value n
    (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n)))
    (a1 a2 a3 b1 b2 : Ty.tySem (Word n)) :
  division_normalized_result n rec ->
  word_modulus (S n) <= 2 * @toZ (WordToZ (S n)) (b1,b2) ->
  (@toZ (WordToZ n) a1 * word_modulus n + @toZ (WordToZ n) a2) * word_modulus n +
    @toZ (WordToZ n) a3 < @toZ (WordToZ (S n)) (b1,b2) * word_modulus n ->
  let z := @div3n2n_approx_spec n Alg.CoreFunSem rec ((a1,a2),b1) in
  @toZ (WordToZ (S n)) (a1,a2) =
    @toZ (WordToZ n) (fst (snd z)) * @toZ (WordToZ n) b1 +
    @toZ (WordToZ n) (snd (snd z)) + word_modulus n * @toZ BitToZ (fst z) /\
  ((fst z = Bit.zero /\ @toZ (WordToZ n) (snd (snd z)) < @toZ (WordToZ n) b1) \/
    @toZ (WordToZ n) (fst (snd z)) = word_modulus n - 1).
Proof.
  intros Hrec Hnorm Hbound. cbn zeta. rewrite div3n2n_approx_unfold.
  pose proof (lt_word_spec_numeric n a1 b1) as Hlt.
  pose proof (division_leading_not_greater n a1 a2 a3 b1 b2 Hbound) as Hle.
  pose proof (word_modulus_positive n) as HM.
  pose proof (word_value_bounds n a2) as HA2.
  destruct (@lt_word_spec Alg.CoreFunSem n (a1,b1)) as [[] | []].
  - change (Datatypes.false = (@toZ (WordToZ n) a1 <? @toZ (WordToZ n) b1)) in Hlt.
    symmetry in Hlt. apply Z.ltb_ge in Hlt.
    assert (Heq : @toZ (WordToZ n) a1 = @toZ (WordToZ n) b1) by lia.
    pose proof (division_add_balance n a2 b1) as Hsum.
    destruct (@Word.adder n Alg.CoreFunSem (a2,b1)) as [c rho].
    change (word_modulus n * @toZ BitToZ c + @toZ (WordToZ n) rho =
      @toZ (WordToZ n) a2 + @toZ (WordToZ n) b1) in Hsum.
    change (@toZ (WordToZ n) a1 * word_modulus n + @toZ (WordToZ n) a2 =
      @toZ (WordToZ n) (@division_high_word n Alg.CoreFunSem tt) * @toZ (WordToZ n) b1 +
      @toZ (WordToZ n) rho + word_modulus n * @toZ BitToZ c /\
      ((c = Bit.zero /\ @toZ (WordToZ n) rho < @toZ (WordToZ n) b1) \/
      @toZ (WordToZ n) (@division_high_word n Alg.CoreFunSem tt) = word_modulus n - 1)).
    rewrite division_high_word_value. split; [nia|right; reflexivity].
  - change (Datatypes.true = (@toZ (WordToZ n) a1 <? @toZ (WordToZ n) b1)) in Hlt.
    symmetry in Hlt. apply Z.ltb_lt in Hlt.
    assert (Hnorm1 : word_modulus n <= 2 * @toZ (WordToZ n) b1)
      by (apply division_leading_normalized with (lo := b2); exact Hnorm).
    assert (Hbound1 : @toZ (WordToZ (S n)) (a1,a2) < @toZ (WordToZ n) b1 * word_modulus n).
    { change (@toZ (WordToZ n) a1 * word_modulus n + @toZ (WordToZ n) a2 <
        @toZ (WordToZ n) b1 * word_modulus n). nia. }
    destruct (Hrec (a1,a2) b1 Hnorm1 Hbound1) as [Hqr HR].
    change (@toZ (WordToZ (S n)) (a1,a2) =
      @toZ (WordToZ n) (fst (rec ((a1,a2),b1))) * @toZ (WordToZ n) b1 +
      @toZ (WordToZ n) (snd (rec ((a1,a2),b1))) + word_modulus n * 0 /\
      (((Bit.zero : Ty.tySem Bit) = Bit.zero /\
        @toZ (WordToZ n) (snd (rec ((a1,a2),b1))) < @toZ (WordToZ n) b1) \/
        @toZ (WordToZ n) (fst (rec ((a1,a2),b1))) = word_modulus n - 1)).
    rewrite Z.mul_0_r, Z.add_0_r.
    split; [symmetry; exact Hqr|left; split; [reflexivity|exact (proj2 HR)]].
Qed.

Lemma div3n2n_builder_unfold n
    (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n)))
    (a1 a2 a3 b1 b2 : Ty.tySem (Word n)) :
  @div3n2n_word_builder n Alg.CoreFunSem rec (((a1,a2),a3),(b1,b2)) =
    @div3n2n_body_spec n Alg.CoreFunSem
      (@div3n2n_approx_spec n Alg.CoreFunSem rec ((a1,a2),b1),(a3,(b1,b2))).
Proof. reflexivity. Qed.

Lemma div3n2n_builder_value n
    (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n)))
    (a1 a2 a3 b1 b2 : Ty.tySem (Word n)) :
  division_normalized_result n rec ->
  word_modulus (S n) <= 2 * @toZ (WordToZ (S n)) (b1,b2) ->
  (@toZ (WordToZ (S n)) (a1,a2)) * word_modulus n + @toZ (WordToZ n) a3 <
    @toZ (WordToZ (S n)) (b1,b2) * word_modulus n ->
  let z := @div3n2n_word_builder n Alg.CoreFunSem rec (((a1,a2),a3),(b1,b2)) in
  @toZ (WordToZ n) (fst z) * @toZ (WordToZ (S n)) (b1,b2) +
    @toZ (WordToZ (S n)) (snd z) =
    @toZ (WordToZ (S n)) (a1,a2) * word_modulus n + @toZ (WordToZ n) a3 /\
  0 <= @toZ (WordToZ (S n)) (snd z) < @toZ (WordToZ (S n)) (b1,b2).
Proof.
  intros Hrec Hnorm Hbound. cbn zeta. rewrite div3n2n_builder_unfold.
  set (s := @div3n2n_approx_spec n Alg.CoreFunSem rec ((a1,a2),b1)).
  assert (Happrox : @toZ (WordToZ (S n)) (a1,a2) =
    @toZ (WordToZ n) (fst (snd s)) * @toZ (WordToZ n) b1 +
    @toZ (WordToZ n) (snd (snd s)) + word_modulus n * @toZ BitToZ (fst s) /\
    ((fst s = Bit.zero /\ @toZ (WordToZ n) (snd (snd s)) < @toZ (WordToZ n) b1) \/
      @toZ (WordToZ n) (fst (snd s)) = word_modulus n - 1)).
  { apply div3n2n_approx_value with (a3 := a3) (b2 := b2); assumption. }
  destruct s as [c [q rho]].
  destruct Happrox as [HA Hcase]. cbn [fst snd] in HA, Hcase.
  set (r := @toZ (WordToZ n) rho + word_modulus n * @toZ BitToZ c).
  pose proof (word_value_bounds n q) as HQ.
  pose proof (word_value_bounds n rho) as Hrho.
  pose proof (word_value_bounds 0 c) as Hc.
  change (0 <= @toZ BitToZ c < 2) in Hc.
  pose proof (word_modulus_positive n) as HB.
  assert (HR : 0 <= r) by (unfold r; nia).
  assert (HAeq : @toZ (WordToZ (S n)) (a1,a2) = @toZ (WordToZ n) q * @toZ (WordToZ n) b1 + r).
  { unfold r. lia. }
  assert (Hrcase : r < @toZ (WordToZ n) b1 \/ @toZ (WordToZ n) q = word_modulus n - 1).
  { destruct Hcase as [[HC Hsmall] | Hmax]; [left|right; exact Hmax].
    unfold r. rewrite HC. change (@toZ (WordToZ n) rho + word_modulus n * 0 < @toZ (WordToZ n) b1).
    lia. }
  set (N := @toZ (WordToZ (S n)) (a1,a2) * word_modulus n + @toZ (WordToZ n) a3).
  set (D := @toZ (WordToZ (S n)) (b1,b2)).
  assert (Hdelta_bound : -2*D <= N - @toZ (WordToZ n) q * D < D).
  { apply (division_approx_residual_bounds (word_modulus n) (@toZ (WordToZ (S n)) (a1,a2))
      N D (@toZ (WordToZ n) a3) (@toZ (WordToZ n) b1) (@toZ (WordToZ n) b2)
      (@toZ (WordToZ n) q) r).
    - apply word_modulus_at_least_two.
    - apply word_value_bounds.
    - apply word_value_bounds.
    - apply word_value_bounds.
    - rewrite <- word_modulus_S. exact Hnorm.
    - reflexivity.
    - reflexivity.
    - exact Hbound.
    - exact HQ.
    - exact HR.
    - exact HAeq.
    - exact Hrcase. }
  assert (Hdelta : N - @toZ (WordToZ n) q * D =
    @toZ (WordToZ n) rho * word_modulus n + @toZ (WordToZ n) a3 -
    @toZ (WordToZ n) q * @toZ (WordToZ n) b2 + word_modulus (S n) * @toZ BitToZ c).
  { unfold N, D.
    change (@toZ (WordToZ (S n)) (a1,a2) * word_modulus n + @toZ (WordToZ n) a3 -
      @toZ (WordToZ n) q * (@toZ (WordToZ n) b1 * word_modulus n + @toZ (WordToZ n) b2) =
      @toZ (WordToZ n) rho * word_modulus n + @toZ (WordToZ n) a3 -
      @toZ (WordToZ n) q * @toZ (WordToZ n) b2 + word_modulus (S n) * @toZ BitToZ c).
    rewrite HA, word_modulus_S. ring. }
  assert (HN : 0 <= @toZ (WordToZ n) q * D + (N - @toZ (WordToZ n) q * D)).
  { replace (@toZ (WordToZ n) q * D + (N - @toZ (WordToZ n) q * D)) with N by ring.
    unfold N. apply Z.add_nonneg_nonneg.
    - apply Z.mul_nonneg_nonneg; [exact (proj1 (word_value_bounds (S n) (a1,a2)))|].
      apply Z.lt_le_incl; exact HB.
    - exact (proj1 (word_value_bounds n a3)). }
  destruct (div3n2n_body_value n q rho a3 b1 b2 c (N - @toZ (WordToZ n) q * D)
    Hdelta Hdelta_bound HN) as [Hbalance Hrem].
  split.
  - transitivity (@toZ (WordToZ n) q * D + (N - @toZ (WordToZ n) q * D));
      [exact Hbalance|ring].
  - exact Hrem.
Qed.

(** The literal shift branches of Programs.Arith.divPreShift/divPostShift.
    These are canonical-program observations, not complete division jets. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Util.Arith.
Require Import C.jet_vector_shift_word C.jet_full_shift_spec.
Require Import C.jet_predicate_spec.
Require Import C.jet_test_value_spec.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Lemma vector_modulus_multiple (T : ToZ.type) m :
  exists k, 0 < k /\ two_power_nat (vector_bits T m) =
    two_power_nat (ToZ.Theory.bitSize T) * k.
Proof.
  induction m as [|m [k [HK HM]]].
  - exists 1. split; [lia|cbn [vector_bits]; ring].
  - exists (two_power_nat (ToZ.Theory.bitSize T) * k * k).
    pose proof (vector_modulus_positive T 0%nat) as HB.
    change (0 < two_power_nat (ToZ.Theory.bitSize T)) in HB.
    split; [nia|]. cbn [vector_bits]. rewrite two_power_nat_plus, HM. ring.
Qed.

Lemma vector_leftmost_zero_bound (T : ToZ.type) m
    (v : Ty.tySem (Vector T (S m))) :
  @toZ T (@Word.leftmost T (S m) Alg.CoreFunSem v) = 0 ->
  vector_value T (S m) v * two_power_nat (ToZ.Theory.bitSize T) <
    two_power_nat (vector_bits T (S m)).
Proof.
  revert v. induction m as [|m IH]; intros [hi lo] Hzero.
  - change (@toZ T hi = 0) in Hzero.
    pose proof (vector_value_range T 0%nat lo) as HL.
    pose proof (vector_modulus_positive T 0%nat) as HB.
    change (0 <= @toZ T lo < two_power_nat (ToZ.Theory.bitSize T)) in HL.
    change (0 < two_power_nat (ToZ.Theory.bitSize T)) in HB.
    cbn [vector_value vector_bits fst snd]. rewrite two_power_nat_plus, Hzero. nia.
  - change (@toZ T (@Word.leftmost T (S m) Alg.CoreFunSem hi) = 0) in Hzero.
    pose proof (IH hi Hzero) as HH.
    pose proof (vector_value_range T (S m) lo) as HL.
    destruct (vector_modulus_multiple T (S m)) as [k [HK HM]].
    pose proof (vector_modulus_positive T 0%nat) as HB.
    change (0 < two_power_nat (ToZ.Theory.bitSize T)) in HB.
    change ((vector_value T (S m) hi * two_power_nat (vector_bits T (S m)) +
      vector_value T (S m) lo) * two_power_nat (ToZ.Theory.bitSize T) <
      two_power_nat (vector_bits T (S m) + vector_bits T (S m))).
    rewrite two_power_nat_plus. rewrite HM in HH, HL |- *.
    assert (HHk : vector_value T (S m) hi < k) by nia.
    assert (Hupper : vector_value T (S m) hi * (two_power_nat (ToZ.Theory.bitSize T) * k) <=
      (k-1) * (two_power_nat (ToZ.Theory.bitSize T) * k)).
    { apply Z.mul_le_mono_nonneg_r; nia. }
    replace (two_power_nat (ToZ.Theory.bitSize T) * k *
      (two_power_nat (ToZ.Theory.bitSize T) * k)) with
      ((two_power_nat (ToZ.Theory.bitSize T) * k * k) *
        two_power_nat (ToZ.Theory.bitSize T)) by ring.
    apply (proj1 (Z.mul_lt_mono_pos_r _ _ _ HB)). nia.
Qed.

Lemma full_left_zero_word_exact n m (v : Ty.tySem (Word (m+n))) :
  @toZ (WordToZ (m+n)) v * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) <
    two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))) ->
  let result := @full_left_word_spec n m Alg.CoreFunSem (v, @Word.zero n Alg.CoreFunSem tt) in
  @toZ (WordToZ n) (fst result) = 0 /\
    @toZ (WordToZ (m+n)) (snd result) =
      @toZ (WordToZ (m+n)) v * two_power_nat (ToZ.Theory.bitSize (WordToZ n)).
Proof.
  intros Hbound. cbn zeta.
  pose proof (vector_value_range (WordToZ (m+n)) 0%nat v) as HV.
  pose proof (vector_modulus_positive (WordToZ n) 0%nat) as HB.
  change (0 <= @toZ (WordToZ (m+n)) v <
    two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n)))) in HV.
  change (0 < two_power_nat (ToZ.Theory.bitSize (WordToZ n))) in HB.
  split.
  - rewrite full_left_word_spec_quotient, Word.zero_correct, Z.add_0_r.
    apply Z.div_small; nia.
  - rewrite full_left_word_spec_remainder, Word.zero_correct, Z.add_0_r.
    apply Z.mod_small; nia.
Qed.

Lemma full_right_zero_word_value n m (v : Ty.tySem (Word (m+n))) :
  let result := @full_right_word_spec n m Alg.CoreFunSem (@Word.zero n Alg.CoreFunSem tt, v) in
  @toZ (WordToZ (m+n)) (fst result) =
    @toZ (WordToZ (m+n)) v / two_power_nat (ToZ.Theory.bitSize (WordToZ n)) /\
  @toZ (WordToZ n) (snd result) =
    @toZ (WordToZ (m+n)) v mod two_power_nat (ToZ.Theory.bitSize (WordToZ n)).
Proof.
  cbn zeta. split.
  - rewrite full_right_word_spec_quotient, Word.zero_correct, Z.mul_0_l, Z.add_0_l.
    reflexivity.
  - rewrite full_right_word_spec_remainder, Word.zero_correct, Z.mul_0_l, Z.add_0_l.
    reflexivity.
Qed.

Definition division_pre_shift_step n m {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S (m+n))) (Word (m+n)))
       (Ty.Prod (Word (S (m+n))) (Word (m+n))) :=
  ((Alg.Core.Combinators.take Alg.Core.Combinators.iden &&& (Alg.Core.Combinators.unit >>> @Word.zero n term)) >>>
    @full_left_word_spec n (S m) term >>> Alg.Core.Combinators.drop Alg.Core.Combinators.iden) &&&
  ((Alg.Core.Combinators.drop Alg.Core.Combinators.iden &&& (Alg.Core.Combinators.unit >>> @Word.zero n term)) >>>
    @full_left_word_spec n m term >>> Alg.Core.Combinators.drop Alg.Core.Combinators.iden).

Definition division_post_shift_step n m {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (m+n)) (Word (m+n)))
       (Ty.Prod (Word (m+n)) (Word (m+n))) :=
  (((Alg.Core.Combinators.unit >>> @Word.zero n term) &&& Alg.Core.Combinators.take Alg.Core.Combinators.iden) >>>
    @full_right_word_spec n m term >>> Alg.Core.Combinators.take Alg.Core.Combinators.iden) &&&
  ((Alg.Core.Combinators.drop Alg.Core.Combinators.iden &&& (Alg.Core.Combinators.unit >>> @Word.zero n term)) >>>
    @full_left_word_spec n m term >>> Alg.Core.Combinators.drop Alg.Core.Combinators.iden).

Lemma division_pre_shift_step_parametric n m : Alg.Core.Parametric (@division_pre_shift_step n m).
Proof.
  intros term1 term2 R. unfold division_pre_shift_step.
  apply Alg.pair_Parametric; apply Alg.comp_Parametric.
  all: first [apply Alg.pair_Parametric | apply Alg.comp_Parametric].
  all: auto with parametricity.
  all: apply full_left_word_spec_parametric.
Qed.

Lemma division_post_shift_step_parametric n m : Alg.Core.Parametric (@division_post_shift_step n m).
Proof.
  intros term1 term2 R. unfold division_post_shift_step.
  apply Alg.pair_Parametric; apply Alg.comp_Parametric.
  all: first [apply Alg.pair_Parametric | apply Alg.comp_Parametric].
  all: auto with parametricity.
  - apply full_right_word_spec_parametric.
  - apply full_left_word_spec_parametric.
Qed.

Lemma division_pre_shift_step_value n m
    (a : Ty.tySem (Word (S (m+n)))) (b : Ty.tySem (Word (m+n))) :
  @toZ (WordToZ (m+n)) b * word_modulus n < word_modulus (m+n) ->
  @toZ (WordToZ (S (m+n))) a < @toZ (WordToZ (m+n)) b * word_modulus (m+n) ->
  let result := @division_pre_shift_step n m Alg.CoreFunSem (a,b) in
  @toZ (WordToZ (S (m+n))) (fst result) = @toZ (WordToZ (S (m+n))) a * word_modulus n /\
  @toZ (WordToZ (m+n)) (snd result) = @toZ (WordToZ (m+n)) b * word_modulus n /\
  @toZ (WordToZ (S (m+n))) (fst result) <
    @toZ (WordToZ (m+n)) (snd result) * word_modulus (m+n).
Proof.
  intros Hden Hnum. cbn zeta.
  pose proof (word_modulus_positive n) as HB.
  pose proof (word_modulus_positive (m+n)) as HM.
  assert (HA : @toZ (WordToZ (S (m+n))) a * word_modulus n < word_modulus (S (m+n))).
  { rewrite word_modulus_S. nia. }
  destruct (full_left_zero_word_exact n (S m) a HA) as [_ HAn].
  destruct (full_left_zero_word_exact n m b Hden) as [_ HBn].
  change (@toZ (WordToZ (S (m+n)))
    (snd (@full_left_word_spec n (S m) Alg.CoreFunSem (a,@Word.zero n Alg.CoreFunSem tt))) =
      @toZ (WordToZ (S (m+n))) a * word_modulus n /\
    @toZ (WordToZ (m+n))
    (snd (@full_left_word_spec n m Alg.CoreFunSem (b,@Word.zero n Alg.CoreFunSem tt))) =
      @toZ (WordToZ (m+n)) b * word_modulus n /\
    @toZ (WordToZ (S (m+n)))
    (snd (@full_left_word_spec n (S m) Alg.CoreFunSem (a,@Word.zero n Alg.CoreFunSem tt))) <
    @toZ (WordToZ (m+n))
    (snd (@full_left_word_spec n m Alg.CoreFunSem (b,@Word.zero n Alg.CoreFunSem tt))) *
      word_modulus (m+n)).
  split; [exact HAn|]. split; [exact HBn|].
  replace (@toZ (WordToZ (S (m+n)))
    (snd (@full_left_word_spec n (S m) Alg.CoreFunSem (a,@Word.zero n Alg.CoreFunSem tt))))
    with (@toZ (WordToZ (S (m+n))) a * word_modulus n) by (symmetry; exact HAn).
  replace (@toZ (WordToZ (m+n))
    (snd (@full_left_word_spec n m Alg.CoreFunSem (b,@Word.zero n Alg.CoreFunSem tt))))
    with (@toZ (WordToZ (m+n)) b * word_modulus n) by (symmetry; exact HBn).
  nia.
Qed.

Lemma division_post_shift_step_value n m
    (a b : Ty.tySem (Word (m+n))) :
  @toZ (WordToZ (m+n)) b * word_modulus n < word_modulus (m+n) ->
  let result := @division_post_shift_step n m Alg.CoreFunSem (a,b) in
  @toZ (WordToZ (m+n)) (fst result) = @toZ (WordToZ (m+n)) a / word_modulus n /\
  @toZ (WordToZ (m+n)) (snd result) = @toZ (WordToZ (m+n)) b * word_modulus n.
Proof.
  intros Hden. cbn zeta.
  destruct (full_right_zero_word_value n m a) as [HAn _].
  destruct (full_left_zero_word_exact n m b Hden) as [_ HBn].
  change (@toZ (WordToZ (m+n))
    (fst (@full_right_word_spec n m Alg.CoreFunSem (@Word.zero n Alg.CoreFunSem tt,a))) =
      @toZ (WordToZ (m+n)) a / word_modulus n /\
    @toZ (WordToZ (m+n))
    (snd (@full_left_word_spec n m Alg.CoreFunSem (b,@Word.zero n Alg.CoreFunSem tt))) =
      @toZ (WordToZ (m+n)) b * word_modulus n).
  split; assumption.
Qed.

Definition division_leftmost_block n m {term : Alg.Core.Algebra} :
  term (Word (m+n)) (Word n) :=
  eq_rect (Vector (Word n) m) (fun V => term V (Word n))
    (@Word.leftmost (Word n) m term) (Word (m+n)) (vector_word_eq n m).

Lemma division_leftmost_block_parametric n m : Alg.Core.Parametric (@division_leftmost_block n m).
Proof.
  intros term1 term2 R. unfold division_leftmost_block.
  generalize (vector_word_eq n m). generalize (Word (m+n)).
  intros V e. destruct e. apply Word.leftmost_Parametric.
Qed.

Lemma cast_projection_core A B C (e : A = C) (f : Ty.Arrow A B) (v : Ty.tySem A) :
  (eq_rect A (fun V => Ty.Arrow V B) f C e) (eq_rect A Ty.tySem v C e) = f v.
Proof. destruct e; reflexivity. Qed.

Lemma division_leftmost_zero_bound n m (b : Ty.tySem (Word (S m+n))) :
  @toZ (WordToZ n) (@division_leftmost_block n (S m) Alg.CoreFunSem b) = 0 ->
  @toZ (WordToZ (S m+n)) b * word_modulus n < word_modulus (S m+n).
Proof.
  intros Hzero.
  set (v := eq_rect _ Ty.tySem b _ (eq_sym (vector_word_eq n (S m)))).
  assert (HS : @division_leftmost_block n (S m) Alg.CoreFunSem
      (eq_rect _ Ty.tySem v _ (vector_word_eq n (S m))) =
      @Word.leftmost (Word n) (S m) Alg.CoreFunSem v).
  { unfold division_leftmost_block. apply cast_projection_core. }
  unfold v in HS at 1. rewrite cast_value_inverse in HS.
  pose proof (f_equal (@toZ (WordToZ n)) HS) as Hobs.
  assert (HZ : @toZ (WordToZ n) (@Word.leftmost (Word n) (S m) Alg.CoreFunSem v) = 0).
  { etransitivity; [symmetry; exact Hobs|exact Hzero]. }
  pose proof (vector_leftmost_zero_bound (WordToZ n) m v HZ) as Hbound.
  rewrite <- vector_word_value, vector_word_bits in Hbound.
  unfold v in Hbound at 1. rewrite cast_value_inverse in Hbound. exact Hbound.
Qed.

Lemma division_zero_guard_bound n m (b : Ty.tySem (Word (S m+n))) :
  Bit.toBool (@is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n (S m) Alg.CoreFunSem b)) = Datatypes.true ->
  @toZ (WordToZ (S m+n)) b * word_modulus n < word_modulus (S m+n).
Proof.
  intros Hzero. rewrite is_zero_word_spec_numeric in Hzero.
  apply Z.eqb_eq in Hzero. apply division_leftmost_zero_bound; exact Hzero.
Qed.

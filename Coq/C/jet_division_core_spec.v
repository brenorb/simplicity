(** Literal Programs.Arith.div3n2n/div2n1n programs, not a numeric replacement.
    Factor div3n2n over its smaller div2n1n call to obtain structural recursion. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_order_spec C.jet_subtract_spec C.jet_multiply_spec.
Require Import C.jet_predicate_spec.
Require Import C.jet_complement_spec.
Require Import C.jet_borrow_unary_word.
Require Import C.jet_division_normalize_spec C.jet_test_value_spec.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition division_high_word n {term : Alg.Core.Algebra} : term Ty.Unit (Word n) :=
  @Word.fill Ty.Unit Bit n term (@Bit.true Ty.Unit term).

Definition div3n2n_approx_spec n {term : Alg.Core.Algebra}
    (rec : term (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) :
  term (Ty.Prod (Word (S n)) (Word n)) (Ty.Prod Bit (Word (S n))) :=
    (((O O H &&& I H) >>> @lt_word_spec term n) &&& H) >>>
    Bit.cond (Bit.false &&& rec)
      (((O I H &&& I H) >>> @Word.adder n term) >>>
        O H &&& ((Alg.Core.Combinators.unit >>> @division_high_word n term) &&& I H)).

Definition div3n2n_loop2_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
  let dec := @decrement_word_spec term n in
  let add2w := @Word.adder (S n) term in
  (I (O (dec >>> I H))) &&& ((O H &&& I I H) >>> add2w >>> I H).

Definition div3n2n_loop1_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
  let dec := @decrement_word_spec term n in
  let add2w := @Word.adder (S n) term in
  (((O H &&& I I H) >>> add2w) &&& I ((O (dec >>> I H)) &&& I H)) >>>
    O O H &&& (O I H &&& I H) >>>
      Bit.cond (I O H &&& O H) (@div3n2n_loop2_spec n term).

Definition div3n2n_loop0_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod Bit (Word (S n))) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
  (O O H &&& (O I H &&& I H)) >>>
    Bit.cond (@div3n2n_loop1_spec n term) (I O H &&& O H).

Definition div3n2n_body_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod Bit (Word (S n))) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
    (O O H &&&
      ((((O I I H &&& I O H) &&& ((O I O H &&& I I I H) >>> @multiply_word_spec n term)) >>>
          @subtract_word_spec term (S n)) &&& (O I O H &&& I I H))) >>>
      Bit.cond (I O H &&& O I H) (@div3n2n_loop0_spec n term).

Definition div3n2n_word_builder n {term : Alg.Core.Algebra}
    (rec : term (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) :
  term (Ty.Prod (Ty.Prod (Word (S n)) (Word n)) (Word (S n)))
       (Ty.Prod (Word n) (Word (S n))) :=
  (((O O H &&& I O H) >>> @div3n2n_approx_spec n term rec) &&& (O I H &&& I H)) >>>
    @div3n2n_body_spec n term.

Definition div2n1n_bit_spec {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word 1) Bit) (Word 1) :=
  (O I H &&& Bit.or (O O H) (Bit.not (I H))) >>>
    (Bit.or (O H) (I H) &&& I H).

Definition div2n1n_conditions n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Word n)) Bit :=
  Bit.and (I (@Word.leftmost Bit n term)) ((O O H &&& I H) >>> @lt_word_spec term n).

Fixpoint div2n1n_word_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Word n)) (Word (S n)) :=
  match n as n return term (Ty.Prod (Word (S n)) (Word n)) (Word (S n)) with
  | Datatypes.O => @div2n1n_bit_spec term
  | Datatypes.S n =>
      let rec := @div3n2n_word_builder n term (@div2n1n_word_spec n term) in
      let body :=
        ((((O O H &&& O I O H) &&& I H) >>> rec) &&& (O I I H &&& I H)) >>>
        (O O H &&& (((O I H &&& I O H) &&& I I H) >>> rec)) >>>
        ((O H &&& I O H) &&& I I H) in
      (@div2n1n_conditions (S n) term &&& H) >>>
        Bit.cond body (Alg.Core.Combinators.unit >>> @division_high_word (S (S n)) term)
  end.

Definition div3n2n_word_spec n {term : Alg.Core.Algebra} :=
  @div3n2n_word_builder n term (@div2n1n_word_spec n term).

Lemma division_high_word_parametric n : Alg.Core.Parametric (@division_high_word n).
Proof. intros term1 term2 R. apply Word.fill_Parametric, Bit.true_Parametric. Qed.

Ltac division_core_parametric :=
  repeat first [assumption | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric |
    apply Alg.unit_Parametric | apply Bit.cond_Parametric | apply Bit.and_Parametric |
    apply Bit.or_Parametric | apply Bit.not_Parametric | apply Bit.false_Parametric |
    apply Bit.true_Parametric | apply Word.zero_Parametric | apply Word.fill_Parametric |
    apply Word.fullAdder_Parametric | apply Word.fullMultiplier_Parametric |
    apply complement_spec_parametric | apply Word.adder_Parametric | apply Word.leftmost_Parametric |
    apply division_high_word_parametric | apply lt_word_spec_parametric |
    apply subtract_word_spec_parametric | apply decrement_word_spec_parametric |
    apply multiply_word_spec_parametric].

Lemma div3n2n_word_builder_parametric n {term1 term2 : Alg.Core.Algebra}
    (R : Alg.Core.Parametric.Rel term1 term2) rec1 rec2 :
  R _ _ rec1 rec2 ->
  R _ _ (@div3n2n_word_builder n term1 rec1) (@div3n2n_word_builder n term2 rec2).
Proof.
  intros Hrec. unfold div3n2n_word_builder, div3n2n_approx_spec,
    div3n2n_body_spec, div3n2n_loop0_spec, div3n2n_loop1_spec, div3n2n_loop2_spec.
  division_core_parametric.
Qed.

Lemma div2n1n_bit_spec_parametric : Alg.Core.Parametric (@div2n1n_bit_spec).
Proof. intros term1 term2 R. unfold div2n1n_bit_spec. division_core_parametric. Qed.

Lemma div2n1n_word_spec_parametric n : Alg.Core.Parametric (@div2n1n_word_spec n).
Proof.
  intros term1 term2 R. induction n as [|n IH].
  - apply div2n1n_bit_spec_parametric.
  - cbn [div2n1n_word_spec]. division_core_parametric.
    all: apply div3n2n_word_builder_parametric; exact IH.
Qed.

Lemma div3n2n_word_spec_parametric n : Alg.Core.Parametric (@div3n2n_word_spec n).
Proof.
  intros term1 term2 R. apply div3n2n_word_builder_parametric.
  apply div2n1n_word_spec_parametric.
Qed.

Lemma div2n1n_bit_observation (a : Ty.tySem (Word 1)) (b : Ty.tySem Bit) :
  let result := @div2n1n_bit_spec Alg.CoreFunSem (a,b) in
  (@toZ BitToZ (fst result), @toZ BitToZ (snd result)) =
    if andb (word_modulus 0 <=? 2 * @toZ BitToZ b)
        (@toZ (WordToZ 1) a <? @toZ BitToZ b * word_modulus 0)
    then (@toZ (WordToZ 1) a / @toZ BitToZ b, @toZ (WordToZ 1) a mod @toZ BitToZ b)
    else (1,1).
Proof.
  destruct a as [hi lo]. destruct hi as [[] | []], lo as [[] | []], b as [[] | []]; reflexivity.
Qed.

Lemma div2n1n_bit_valid (a : Ty.tySem (Word 1)) (b : Ty.tySem Bit) :
  0 < @toZ BitToZ b -> @toZ (WordToZ 1) a < 2 * @toZ BitToZ b ->
  let result := @div2n1n_bit_spec Alg.CoreFunSem (a,b) in
  @toZ BitToZ (fst result) = @toZ (WordToZ 1) a / @toZ BitToZ b /\
  @toZ BitToZ (snd result) = @toZ (WordToZ 1) a mod @toZ BitToZ b.
Proof.
  destruct a as [hi lo]. destruct hi as [[] | []], lo as [[] | []], b as [[] | []];
    cbn; intros; try lia; split; reflexivity.
Qed.

Definition div_mod_word_spec n {term : Alg.Core.Algebra} :
  term (Word (S n)) (Word (S n)) :=
  (I (@is_zero_word_spec n term) &&& H) >>>
  Bit.cond (I H &&& O H)
    (((((Alg.Core.Combinators.unit >>> @Word.zero n term) &&& O H) &&& I H) >>>
      @division_pre_shift_spec n 0 term >>> @div2n1n_word_spec n term) &&& I H >>>
    O O H &&& ((O I H &&& I H) >>> @division_post_shift_spec n 0 term >>> O H)).

Definition divide_word_spec n {term : Alg.Core.Algebra} :=
  @div_mod_word_spec n term >>> O H.
Definition modulo_word_spec n {term : Alg.Core.Algebra} :=
  @div_mod_word_spec n term >>> I H.
Definition divides_word_spec n {term : Alg.Core.Algebra} :=
  (I H &&& O H) >>> @modulo_word_spec n term >>> @is_zero_word_spec n term.

Lemma div_mod_word_spec_parametric n : Alg.Core.Parametric (@div_mod_word_spec n).
Proof.
  intros term1 term2 R. unfold div_mod_word_spec. division_core_parametric.
  all: first [apply div2n1n_word_spec_parametric | apply division_pre_shift_spec_parametric |
    apply division_post_shift_spec_parametric | apply predicate_spec_parametric].
Qed.

Lemma divide_word_spec_parametric n : Alg.Core.Parametric (@divide_word_spec n).
Proof.
  intros term1 term2 R. apply Alg.comp_Parametric;
    [apply div_mod_word_spec_parametric|apply Alg.take_Parametric, Alg.iden_Parametric].
Qed.

Lemma modulo_word_spec_parametric n : Alg.Core.Parametric (@modulo_word_spec n).
Proof.
  intros term1 term2 R. apply Alg.comp_Parametric;
    [apply div_mod_word_spec_parametric|apply Alg.drop_Parametric, Alg.iden_Parametric].
Qed.

Lemma divides_word_spec_parametric n : Alg.Core.Parametric (@divides_word_spec n).
Proof.
  intros term1 term2 R. unfold divides_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric;
      [apply Alg.drop_Parametric|apply Alg.take_Parametric]; apply Alg.iden_Parametric.
  - apply Alg.comp_Parametric; [apply modulo_word_spec_parametric|apply is_zero_word_spec_parametric].
Qed.

Lemma canonical_is_zero_of_zero n :
  @is_zero_word_spec n Alg.CoreFunSem (@Word.zero n Alg.CoreFunSem tt) = Bit.one.
Proof.
  pose proof (is_zero_word_spec_numeric n (@Word.zero n Alg.CoreFunSem tt)) as Hzero.
  rewrite Word.zero_correct in Hzero.
  destruct (@is_zero_word_spec n Alg.CoreFunSem (@Word.zero n Alg.CoreFunSem tt)) as [[] | []];
    [discriminate|reflexivity].
Qed.

Lemma div_mod_word_zero n (a : Ty.tySem (Word n)) :
  @div_mod_word_spec n Alg.CoreFunSem (a,@Word.zero n Alg.CoreFunSem tt) =
    (@Word.zero n Alg.CoreFunSem tt,a).
Proof.
  unfold div_mod_word_spec.
  cbn -[is_zero_word_spec division_pre_shift_spec div2n1n_word_spec division_post_shift_spec Word.zero].
  rewrite canonical_is_zero_of_zero. reflexivity.
Qed.

Lemma division_word_modulus_even n : exists k, 0 < k /\ word_modulus n = 2*k.
Proof.
  induction n as [|n [k [HK HE]]].
  - exists 1; split; [lia|reflexivity].
  - exists (2*k*k). split; [nia|rewrite word_modulus_S, HE; ring].
Qed.

Lemma division_msb_threshold n (b : Ty.tySem (Word n)) :
  Bit.toBool (@Word.leftmost Bit n Alg.CoreFunSem b) =
    negb (2 * @toZ (WordToZ n) b <? word_modulus n).
Proof.
  revert b. induction n as [|n IH]; intros b.
  - destruct b as [[] | []]; reflexivity.
  - destruct b as [hi lo].
    change (Bit.toBool (@Word.leftmost Bit n Alg.CoreFunSem hi) =
      negb (2 * (@toZ (WordToZ n) hi * word_modulus n + @toZ (WordToZ n) lo) <?
        word_modulus (S n))).
    rewrite IH, word_modulus_S.
    pose proof (word_value_bounds n lo) as HL.
    destruct (division_word_modulus_even n) as [k [HK HE]].
    rewrite HE in HL |- *.
    destruct (2 * @toZ (WordToZ n) hi <? 2*k) eqn:HH.
    + apply Z.ltb_lt in HH.
      assert (HB : (2 * (@toZ (WordToZ n) hi * (2*k) + @toZ (WordToZ n) lo) <? (2*k)*(2*k)) =
        Datatypes.true) by (apply Z.ltb_lt; nia).
      rewrite HB. reflexivity.
    + apply Z.ltb_ge in HH.
      assert (HB : (2 * (@toZ (WordToZ n) hi * (2*k) + @toZ (WordToZ n) lo) <? (2*k)*(2*k)) =
        Datatypes.false) by (apply Z.ltb_ge; nia).
      rewrite HB. reflexivity.
Qed.

Lemma division_normalized_msb n (b : Ty.tySem (Word n)) :
  word_modulus n <= 2 * @toZ (WordToZ n) b ->
  @Word.leftmost Bit n Alg.CoreFunSem b = Bit.one.
Proof.
  intros Hbound. pose proof (division_msb_threshold n b) as Hmsb.
  assert (HB : (2 * @toZ (WordToZ n) b <? word_modulus n) = Datatypes.false)
    by (apply Z.ltb_ge; exact Hbound).
  rewrite HB in Hmsb.
  destruct (@Word.leftmost Bit n Alg.CoreFunSem b) as [[] | []]; [discriminate|reflexivity].
Qed.

Lemma division_high_less n (a : Ty.tySem (Word (S n))) (b : Ty.tySem (Word n)) :
  Bit.toBool (@lt_word_spec Alg.CoreFunSem n (fst a,b)) =
    (@toZ (WordToZ (S n)) a <? @toZ (WordToZ n) b * word_modulus n).
Proof.
  destruct a as [hi lo]. rewrite lt_word_spec_numeric.
  change ((@toZ (WordToZ n) hi <? @toZ (WordToZ n) b) =
    (@toZ (WordToZ n) hi * word_modulus n + @toZ (WordToZ n) lo <?
      @toZ (WordToZ n) b * word_modulus n)).
  pose proof (word_modulus_positive n) as HM.
  pose proof (word_value_bounds n lo) as HL.
  destruct (@toZ (WordToZ n) hi <? @toZ (WordToZ n) b) eqn:HC; symmetry.
  - apply Z.ltb_lt in HC. apply Z.ltb_lt; nia.
  - apply Z.ltb_ge in HC. apply Z.ltb_ge; nia.
Qed.

Lemma div2n1n_conditions_parametric n : Alg.Core.Parametric (@div2n1n_conditions n).
Proof. intros term1 term2 R. unfold div2n1n_conditions. division_core_parametric. Qed.

Lemma div2n1n_conditions_observation n (a : Ty.tySem (Word (S n))) (b : Ty.tySem (Word n)) :
  Bit.toBool (@div2n1n_conditions n Alg.CoreFunSem (a,b)) =
  andb (negb (2 * @toZ (WordToZ n) b <? word_modulus n))
    (@toZ (WordToZ (S n)) a <? @toZ (WordToZ n) b * word_modulus n).
Proof.
  assert (Hbool : Bit.toBool (@div2n1n_conditions n Alg.CoreFunSem (a,b)) =
    andb (Bit.toBool (@Word.leftmost Bit n Alg.CoreFunSem b))
      (Bit.toBool (@lt_word_spec Alg.CoreFunSem n (fst a,b)))).
  { change (Bit.toBool (match @Word.leftmost Bit n Alg.CoreFunSem b with
      | inl _ => Bit.zero
      | inr _ => @lt_word_spec Alg.CoreFunSem n (fst a,b)
      end) = andb (Bit.toBool (@Word.leftmost Bit n Alg.CoreFunSem b))
        (Bit.toBool (@lt_word_spec Alg.CoreFunSem n (fst a,b)))).
    destruct (@Word.leftmost Bit n Alg.CoreFunSem b) as [[] | []],
      (@lt_word_spec Alg.CoreFunSem n (fst a,b)) as [[] | []]; reflexivity. }
  rewrite Hbool, division_msb_threshold, division_high_less. reflexivity.
Qed.

Lemma div2n1n_conditions_valid n (a : Ty.tySem (Word (S n))) (b : Ty.tySem (Word n)) :
  word_modulus n <= 2 * @toZ (WordToZ n) b ->
  @toZ (WordToZ (S n)) a < @toZ (WordToZ n) b * word_modulus n ->
  @div2n1n_conditions n Alg.CoreFunSem (a,b) = Bit.one.
Proof.
  intros HM HA. pose proof (div2n1n_conditions_observation n a b) as Hguard.
  assert (HD : (2 * @toZ (WordToZ n) b <? word_modulus n) = Datatypes.false)
    by (apply Z.ltb_ge; exact HM).
  assert (HN : (@toZ (WordToZ (S n)) a <? @toZ (WordToZ n) b * word_modulus n) = Datatypes.true)
    by (apply Z.ltb_lt; exact HA).
  rewrite HD, HN in Hguard.
  destruct (@div2n1n_conditions n Alg.CoreFunSem (a,b)) as [[] | []]; [discriminate|reflexivity].
Qed.

Lemma division_plain_input_guard n (a b : Ty.tySem (Word n)) :
  0 < @toZ (WordToZ n) b ->
  @div2n1n_conditions n Alg.CoreFunSem
    (@division_pre_shift_spec n 0 Alg.CoreFunSem ((@Word.zero n Alg.CoreFunSem tt,a),b)) = Bit.one.
Proof.
  intros HB.
  destruct (division_plain_input_normalization n a (@Word.zero n Alg.CoreFunSem tt) b HB)
    as [k [HK [HA [HD [HR [Hsame [Hlead Hbound]]]]]]].
  destruct (@division_pre_shift_spec n 0 Alg.CoreFunSem ((@Word.zero n Alg.CoreFunSem tt,a),b))
    as [x y] eqn:HP.
  apply div2n1n_conditions_valid; assumption.
Qed.

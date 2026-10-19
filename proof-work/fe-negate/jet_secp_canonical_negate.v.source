(** Literal field negation and 512-bit normalization from the pinned Haskell.
    These program bridges are support, not standalone public C jet coverage. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_canonical_normalize C.jet_multiply_spec.
Require Import C.jet_division_core_spec C.jet_division_result_spec C.jet_division_value.
Require Import C.jet_predicate_spec.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition canonical_fe_normalize512 {term : Alg.Core.Algebra} :
    term (Word 9) (Word 8) :=
  iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word))
    >>> @modulo_word_spec 9 term >>> I H.
Definition canonical_fe_multiply {term : Alg.Core.Algebra} :
    term (Ty.Prod (Word 8) (Word 8)) (Word 8) :=
  @multiply_word_spec 8 term >>> @canonical_fe_normalize512 term.
Definition canonical_negate_factor : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) ((-1) mod canonical_field_order).
Definition canonical_fe_negate {term : Alg.Core.Algebra} :
    term (Word 8) (Word 8) :=
  Alg.scribe canonical_negate_factor &&& iden >>> @canonical_fe_multiply term.

Lemma canonical_fe_normalize512_step (x : Ty.tySem (Word 9)) :
  @canonical_fe_normalize512 Alg.CoreFunSem x =
  snd (@modulo_word_spec 9 Alg.CoreFunSem
    (x, (@Word.zero 8 Alg.CoreFunSem tt, canonical_field_word))).
Proof.
  unfold canonical_fe_normalize512.
  cbn -[modulo_word_spec Word.zero canonical_field_word Alg.scribe].
  rewrite Alg.scribe_correct. reflexivity.
Qed.

Local Opaque modulo_word_spec canonical_field_word.

Lemma canonical_512_divisor_value :
  @toZ (WordToZ 9) (@Word.zero 8 Alg.CoreFunSem tt, canonical_field_word) =
    canonical_field_order.
Proof.
  change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt) *
    word_modulus 8 + @toZ (WordToZ 8) canonical_field_word = canonical_field_order).
  rewrite Word.zero_correct, canonical_field_word_value. ring.
Qed.

Lemma canonical_fe_normalize512_numeric (x : Ty.tySem (Word 9)) :
  @toZ (WordToZ 8) (@canonical_fe_normalize512 Alg.CoreFunSem x) =
  @toZ (WordToZ 9) x mod canonical_field_order.
Proof.
  rewrite canonical_fe_normalize512_step.
  set (r := @modulo_word_spec 9 Alg.CoreFunSem
    (x, (@Word.zero 8 Alg.CoreFunSem tt, canonical_field_word))).
  pose proof (division_word_spec_numeric 9 Datatypes.true x
    (@Word.zero 8 Alg.CoreFunSem tt, canonical_field_word)) as HR.
  change (@toZ (WordToZ 9) r =
    division_numeric Datatypes.true (@toZ (WordToZ 9) x)
      (@toZ (WordToZ 9) (@Word.zero 8 Alg.CoreFunSem tt, canonical_field_word))) in HR.
  rewrite canonical_512_divisor_value in HR.
  assert (HP : 0 < canonical_field_order) by (pose proof canonical_field_order_range; lia).
  assert (E : (canonical_field_order =? 0) = Datatypes.false) by (apply Z.eqb_neq; lia).
  unfold division_numeric in HR. rewrite E in HR.
  destruct r as [hi lo].
  change (@toZ (WordToZ 8) hi * word_modulus 8 + @toZ (WordToZ 8) lo =
    @toZ (WordToZ 9) x mod canonical_field_order) in HR.
  pose proof (word_value_bounds 8 hi) as HH.
  pose proof (word_value_bounds 8 lo) as HL.
  pose proof (Z.mod_pos_bound (@toZ (WordToZ 9) x) canonical_field_order HP) as HM.
  pose proof canonical_field_order_range as HPRange.
  change (@toZ (WordToZ 8) lo = @toZ (WordToZ 9) x mod canonical_field_order).
  destruct (Z.eq_dec (@toZ (WordToZ 8) hi) 0) as [HZ|HZ].
  - rewrite HZ in HR. lia.
  - assert (1 <= @toZ (WordToZ 8) hi) by lia.
    exfalso. nia.
Qed.
Print Assumptions canonical_fe_normalize512_numeric.

Lemma canonical_negate_factor_value :
  @toZ (WordToZ 8) canonical_negate_factor = canonical_field_order - 1.
Proof.
  destruct canonical_field_order_range as [[HP HM] _].
  assert (HE : (-1) mod canonical_field_order = canonical_field_order - 1).
  { replace (-1) with ((canonical_field_order - 1) + (-1) * canonical_field_order) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small; lia. }
  unfold canonical_negate_factor. rewrite HE, to_fromZ.
  apply Z.mod_small. change (0 <= canonical_field_order - 1 < word_modulus 8). lia.
Qed.

Lemma canonical_fe_negate_step (x : Ty.tySem (Word 8)) :
  @canonical_fe_negate Alg.CoreFunSem x =
  @canonical_fe_normalize512 Alg.CoreFunSem
    (@multiply_word_spec 8 Alg.CoreFunSem (canonical_negate_factor, x)).
Proof.
  unfold canonical_fe_negate, canonical_fe_multiply.
  cbn -[canonical_fe_normalize512 multiply_word_spec canonical_negate_factor Alg.scribe].
  rewrite Alg.scribe_correct. reflexivity.
Qed.

Lemma canonical_fe_negate_numeric (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@canonical_fe_negate Alg.CoreFunSem x) =
  (canonical_field_order - @toZ (WordToZ 8) x) mod canonical_field_order.
Proof.
  rewrite canonical_fe_negate_step, canonical_fe_normalize512_numeric,
    multiply_word_spec_numeric, canonical_negate_factor_value.
  pose proof canonical_field_order_range as HP.
  replace ((canonical_field_order - 1) * @toZ (WordToZ 8) x) with
    (- @toZ (WordToZ 8) x + @toZ (WordToZ 8) x * canonical_field_order) by ring.
  replace (canonical_field_order - @toZ (WordToZ 8) x) with
    (- @toZ (WordToZ 8) x + 1 * canonical_field_order) by ring.
  rewrite !Z.mod_add by lia. reflexivity.
Qed.
Print Assumptions canonical_fe_negate_numeric.

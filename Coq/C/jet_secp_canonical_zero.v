(** Literal canonical zero test, including the field-order input branch. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_test_value_spec C.jet_equality_spec C.jet_predicate_spec.
Require Import C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Definition canonical_fe_is_zero {term : Alg.Core.Algebra} : term (Word 8) Bit :=
  Bit.or (@is_zero_word_spec 8 term)
    (((unit >>> Alg.scribe canonical_field_word) &&& iden) >>> @equality_spec (Word 8) term).
Local Opaque is_zero_word_spec equality_spec canonical_field_word canonical_fe_normalize.

Lemma canonical_fe_is_zero_numeric (value : Ty.tySem (Word 8)) :
  Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value) =
    orb (Z.eqb (@toZ (WordToZ 8) value) 0)
      (Z.eqb (@toZ (WordToZ 8) value) canonical_field_order).
Proof.
  change (Bit.toBool (match @is_zero_word_spec 8 Alg.CoreFunSem value with
      | inl _ => @equality_spec (Word 8) Alg.CoreFunSem
          (@Alg.scribe Ty.Unit (Word 8) canonical_field_word Alg.CoreFunSem tt, value)
      | inr _ => inr tt end) =
      orb (Z.eqb (@toZ (WordToZ 8) value) 0)
        (Z.eqb (@toZ (WordToZ 8) value) canonical_field_order)).
  rewrite Alg.scribe_correct.
  assert (HOr : Bit.toBool (match @is_zero_word_spec 8 Alg.CoreFunSem value with
      | inl _ => @equality_spec (Word 8) Alg.CoreFunSem (canonical_field_word, value)
      | inr _ => inr tt end) =
      orb (Bit.toBool (@is_zero_word_spec 8 Alg.CoreFunSem value))
        (Bit.toBool (@equality_spec (Word 8) Alg.CoreFunSem (canonical_field_word, value)))).
  { destruct (@is_zero_word_spec 8 Alg.CoreFunSem value) as [z|z]; destruct z; reflexivity. }
  rewrite HOr, is_zero_word_spec_numeric, equality_spec_word_numeric,
    canonical_field_word_value.
  rewrite (Z.eqb_sym canonical_field_order (@toZ (WordToZ 8) value)); reflexivity.
Qed.

Lemma word_mod_field_zero value :
  0 <= value < word_modulus 8 ->
  Z.eqb (value mod canonical_field_order) 0 =
    orb (Z.eqb value 0) (Z.eqb value canonical_field_order).
Proof.
  intros HValue. destruct canonical_field_order_range as [[HP HM] HTwice].
  destruct (Z.ltb_spec value canonical_field_order).
  - rewrite Z.mod_small by lia.
    rewrite (proj2 (Z.eqb_neq value canonical_field_order)) by lia.
    symmetry; apply Bool.orb_false_r.
  - replace value with ((value - canonical_field_order) + 1 * canonical_field_order)%Z at 1 by ring.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    destruct (Z.eqb_spec (value - canonical_field_order) 0),
      (Z.eqb_spec value 0), (Z.eqb_spec value canonical_field_order); try reflexivity; exfalso; lia.
Qed.

Lemma canonical_fe_zero_after_normalize (value : Ty.tySem (Word 8)) :
  Z.eqb (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)) 0 =
    Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value).
Proof.
  rewrite canonical_fe_normalize_numeric, canonical_fe_is_zero_numeric.
  apply word_mod_field_zero; apply word_value_bounds.
Qed.

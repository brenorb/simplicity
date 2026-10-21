(** Literal LibSecp256k1.gej_x_equiv, retaining the infinity guard and
    subtraction-via-negation tree. This is a target bridge, not a C jet proof. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_literal.
Require Import C.jet_secp_literal_gej_predicate C.jet_literal_division_parametric.
Require Import C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric.
Require Import C.jet_secp_negate_literal_contract C.jet_secp_square_execution C.jet_secp_multiply_literal_spec.
Require Import C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_gej_x_equiv {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) (Ty.Sum Ty.Unit Ty.Unit) :=
  Bit.and (Bit.not (I (@literal_gej_is_infinity term)))
    ((I (O (O (@literal_fe_negate term)))) &&&
      ((I (I (@literal_fe_square term))) &&& O H >>> @literal_fe_multiply term)
      >>> @literal_fe_add term >>> @canonical_fe_is_zero term).
Local Opaque literal_fe_negate literal_fe_square literal_fe_multiply literal_fe_add canonical_fe_is_zero.

Lemma literal_x_equiv_step (q x y z : Ty.tySem (Word 8)) :
  Bit.toBool (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z))) =
  andb (negb (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))
    (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
      (@literal_fe_add Alg.CoreFunSem
        (@literal_fe_negate Alg.CoreFunSem x,
          @literal_fe_multiply Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem z,q))))).
Proof.
  unfold literal_gej_x_equiv, literal_gej_is_infinity.
  cbn -[literal_fe_negate literal_fe_square literal_fe_multiply literal_fe_add canonical_fe_is_zero].
  destruct (@canonical_fe_is_zero Alg.CoreFunSem z) as [[] | []]; reflexivity.
Qed.

Lemma x_equiv_mod_neg_add a b :
  Z.eqb (((feP-a) mod feP + b mod feP) mod feP) 0 = Z.eqb (a mod feP) (b mod feP).
Proof.
  pose proof (curve_mod_add_neg_eq b a 0) as HEq.
  rewrite Z.add_0_l, Z.add_0_r, Zminus_mod_idemp_r in HEq.
  rewrite Z.add_comm; exact HEq.
Qed.

Lemma literal_x_equiv_numeric (q x y z : Ty.tySem (Word 8)) :
  Bit.toBool (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z))) =
    andb (negb (Z.eqb (@toZ (WordToZ 8) z mod feP) 0))
      (Z.eqb (@toZ (WordToZ 8) x mod feP)
        ((@toZ (WordToZ 8) z * @toZ (WordToZ 8) z * @toZ (WordToZ 8) q) mod feP)).
Proof.
  rewrite literal_x_equiv_step, !literal_curve_zero_numeric, literal_fe_add_numeric,
    canonical_field_order_matches_limb_model, literal_curve_negate_numeric,
    literal_multiply_numeric, literal_square_numeric.
  rewrite Z.mod_mod, Z.mul_mod_idemp_l by (unfold feP,feR;lia).
  rewrite x_equiv_mod_neg_add; reflexivity.
Qed.

Lemma literal_gej_x_equiv_parametric : Alg.Core.Parametric (@literal_gej_x_equiv).
Proof.
  intros term1 term2 R. unfold literal_gej_x_equiv.
  apply Bit.and_Parametric.
  - apply Bit.not_Parametric, Alg.drop_Parametric, literal_gej_is_infinity_parametric.
  - repeat first [apply literal_fe_negate_parametric|apply curve_square_parametric|
      apply literal_fe_multiply_parametric|apply literal_fe_add_parametric|
      apply canonical_fe_is_zero_parametric|apply Alg.comp_Parametric|
      apply Alg.pair_Parametric|apply Alg.take_Parametric|apply Alg.drop_Parametric|
      apply Alg.iden_Parametric].
Qed.
Print Assumptions literal_x_equiv_numeric.
Print Assumptions literal_gej_x_equiv_parametric.

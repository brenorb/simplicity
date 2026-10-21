(** Literal canonical Core trees, retaining both projective and affine routing.
    Specification bridges here support the original C implementation proof. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_canonical_normalize C.jet_secp_canonical_negate.
Require Import C.jet_secp_negate_literal_contract C.jet_secp_square_execution C.jet_secp_multiply_literal_spec.
Require Import C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric.
Require Import C.jet_secp_canonical_zero C.jet_secp_rescale_literal.
Require Import C.jet_literal_division_parametric C.jet_secp_literal_gej_predicate.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition curve_seven_word : Ty.tySem (Word 8) := @fromZ (WordToZ 8) 7.
Definition literal_gej_is_on_curve {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) Bit :=
  (((unit >>> Alg.scribe curve_seven_word) &&&
      (I H >>> @literal_fe_cube term >>> @literal_fe_square term) >>> @literal_fe_multiply term) &&&
    (O (O (@literal_fe_cube term) &&& (I (@literal_fe_square term) >>> @literal_fe_negate term))
      >>> @literal_fe_add term)) >>> @literal_fe_add term >>> @canonical_fe_is_zero term.
Definition literal_ge_is_on_curve {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word 8) (Word 8)) Bit :=
  iden &&& (unit >>> @literal_fe_one256 term) >>> @literal_gej_is_on_curve term.

Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
  literal_fe_negate literal_fe_one256 canonical_fe_is_zero.

Lemma curve_seven_value : @toZ (WordToZ 8) curve_seven_word = 7.
Proof. vm_compute; reflexivity. Qed.
Lemma literal_gej_curve_step (x y z : Ty.tySem (Word 8)) :
  @literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z) =
    @canonical_fe_is_zero Alg.CoreFunSem
      (@literal_fe_add Alg.CoreFunSem
        (@literal_fe_multiply Alg.CoreFunSem
          (curve_seven_word,@literal_fe_square Alg.CoreFunSem (@literal_fe_cube Alg.CoreFunSem z)),
         @literal_fe_add Alg.CoreFunSem
           (@literal_fe_cube Alg.CoreFunSem x,
            @literal_fe_negate Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem y)))).
Proof.
  unfold literal_gej_is_on_curve.
  cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
    literal_fe_negate canonical_fe_is_zero Alg.scribe curve_seven_word].
  rewrite Alg.scribe_correct. reflexivity.
Qed.
Lemma literal_ge_curve_step (x y : Ty.tySem (Word 8)) :
  @literal_ge_is_on_curve Alg.CoreFunSem (x,y) =
    @literal_gej_is_on_curve Alg.CoreFunSem ((x,y),@literal_fe_one256 Alg.CoreFunSem tt).
Proof. reflexivity. Qed.

Lemma literal_curve_cube_numeric (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem x) =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod feP.
Proof.
  change (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
    (x,@literal_fe_square Alg.CoreFunSem x)) =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod feP).
  rewrite literal_multiply_numeric, literal_square_numeric.
  rewrite Z.mul_mod_idemp_r by (unfold feP,feR; discriminate).
  f_equal; ring.
Qed.

Lemma literal_curve_negate_numeric (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem x) =
    (feP - @toZ (WordToZ 8) x) mod feP.
Proof. rewrite literal_fe_negate_matches, canonical_fe_negate_numeric, canonical_field_order_matches_limb_model. reflexivity. Qed.
Lemma literal_curve_zero_numeric (x : Ty.tySem (Word 8)) :
  Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem x) = Z.eqb (@toZ (WordToZ 8) x mod feP) 0.
Proof.
  rewrite <- canonical_fe_zero_after_normalize, canonical_fe_normalize_numeric,
    canonical_field_order_matches_limb_model. reflexivity.
Qed.

Lemma curve_mod_add_neg_eq a b k :
  Z.eqb ((k + (a mod feP + (feP-b mod feP) mod feP)) mod feP) 0 =
    Z.eqb (b mod feP) ((a+k) mod feP).
Proof.
  replace (k + (a mod feP + (feP-b mod feP) mod feP)) with
    ((k + a mod feP) + (feP-b mod feP) mod feP) by ring.
  rewrite Z.add_mod_idemp_r by (unfold feP,feR; lia).
  replace (k+a mod feP+(feP-b mod feP)) with
    ((feP-b mod feP+k)+a mod feP) by ring.
  rewrite Z.add_mod_idemp_r by (unfold feP,feR; lia).
  replace (feP-b mod feP+k+a) with ((a+k+feP)-b mod feP) by ring.
  rewrite Zminus_mod_idemp_r.
  replace (a+k+feP-b) with ((a+k-b)+1*feP) by ring.
  rewrite Z.mod_add, Zminus_mod by (unfold feP,feR; lia).
  apply Bool.eq_true_iff_eq. rewrite !Z.eqb_eq.
  rewrite Z.mod_divide by (unfold feP,feR; lia).
  pose proof (Z.mod_pos_bound b feP ltac:(unfold feP,feR; lia)) as HB.
  pose proof (Z.mod_pos_bound (a+k) feP ltac:(unfold feP,feR; lia)) as HA.
  split.
  - intros [q HQ]. unfold feP,feR in *; nia.
  - intro HE; rewrite HE. exists 0; ring.
Qed.

Lemma literal_ge_curve_numeric (x y : Ty.tySem (Word 8)) :
  Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y)) =
    Z.eqb ((@toZ (WordToZ 8) y * @toZ (WordToZ 8) y) mod feP)
      ((@toZ (WordToZ 8) x * @toZ (WordToZ 8) x * @toZ (WordToZ 8) x + 7) mod feP).
Proof.
  rewrite literal_ge_curve_step, literal_gej_curve_step, literal_curve_zero_numeric.
  rewrite !literal_fe_add_numeric, canonical_field_order_matches_limb_model.
  rewrite literal_multiply_numeric, !literal_square_numeric,
    !literal_curve_cube_numeric, literal_curve_negate_numeric,
    literal_square_numeric, literal_fe_one256_value, curve_seven_value.
  assert (HC : ((1*1*1) mod feP * ((1*1*1) mod feP)) mod feP = 1).
  { vm_compute; reflexivity. }
  rewrite HC.
  change (7*1) with 7.
  rewrite (Z.mod_small 7 feP) by (unfold feP,feR; lia).
  repeat rewrite Z.mod_mod by (unfold feP,feR; lia).
  repeat rewrite Z.add_mod_idemp_r by (unfold feP,feR; lia).
  repeat rewrite Z.add_mod_idemp_l by (unfold feP,feR; lia).
  apply curve_mod_add_neg_eq.
Qed.

Local Transparent literal_fe_square literal_fe_cube.
Lemma curve_square_parametric : Alg.Core.Parametric (@literal_fe_square).
Proof.
  intros term1 term2 R. unfold literal_fe_square.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; apply Alg.iden_Parametric.
  - apply literal_fe_multiply_parametric.
Qed.
Lemma curve_cube_parametric : Alg.Core.Parametric (@literal_fe_cube).
Proof.
  intros term1 term2 R. unfold literal_fe_cube.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.iden_Parametric|apply curve_square_parametric].
  - apply literal_fe_multiply_parametric.
Qed.
Lemma literal_gej_is_on_curve_parametric : Alg.Core.Parametric (@literal_gej_is_on_curve).
Proof.
  intros term1 term2 R. unfold literal_gej_is_on_curve.
  repeat first [apply Alg.scribe_Parametric | apply curve_cube_parametric |
    apply curve_square_parametric | apply literal_fe_multiply_parametric |
    apply literal_fe_add_parametric | apply literal_fe_negate_parametric |
    apply canonical_fe_is_zero_parametric | apply Alg.comp_Parametric |
    apply Alg.pair_Parametric | apply Alg.take_Parametric |
    apply Alg.drop_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.
Lemma literal_ge_is_on_curve_parametric : Alg.Core.Parametric (@literal_ge_is_on_curve).
Proof.
  intros term1 term2 R. unfold literal_ge_is_on_curve.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.iden_Parametric|].
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply literal_fe_one256_parametric].
  - apply literal_gej_is_on_curve_parametric.
Qed.

Print Assumptions literal_ge_curve_numeric.
Print Assumptions literal_gej_is_on_curve_parametric.
Print Assumptions literal_ge_is_on_curve_parametric.

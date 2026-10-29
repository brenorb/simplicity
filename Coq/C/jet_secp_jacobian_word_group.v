(** Interpret the original literal doubling program in the curve group,
    retaining its infinity branch and arbitrary shared-Z context. The C-call
    execution proof and the remaining Strauss operations are separate. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_jacobian_group C.jet_secp_jacobian_double_group C.jet_secp_double_literal.
Require Import C.jet_secp_field_word_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_word_group_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Definition secp_jacobian_word_fields (j:Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))):=
 ((secp_field_word (fst (fst j)),secp_field_word (snd (fst j))),secp_field_word (snd j)).
Lemma secp_literal_double_body_fields (x y z:Ty.tySem (Word 8)):
 secp_jacobian_word_fields (@literal_gej_double_body Alg.CoreFunSem ((x,y),z))=
 ((secp_jdouble_x (secp_field_word x) (secp_field_word y),
   secp_jdouble_y (secp_field_word x) (secp_field_word y)),
   GZnZ.mul feP (secp_field_word y) (secp_field_word z)).
Proof.
 rewrite literal_gej_double_body_step.
 unfold secp_jacobian_word_fields;cbn zeta;cbn [fst snd].
 repeat first [rewrite secp_field_word_add|rewrite secp_field_word_mul|
  rewrite secp_field_word_square|rewrite secp_field_word_negate|rewrite secp_field_word_halve|
  rewrite secp_field_word_multiply_int|rewrite secp_field_integer_two|rewrite secp_field_integer_three].
 f_equal;f_equal;unfold secp_jdouble_y,secp_jdouble_x,secp_jdouble_slope,secp_group_field;
 field;exact (SMain.two_not_zero secp_group_theory).
Qed.
Require Import C.jet_secp_literal_infinity C.jet_secp_literal_gej_predicate.
Definition secp_jacobian_context_rep (c:secp_group_field)
 (j:(secp_group_field*secp_group_field)*secp_group_field) (p:secp_group_point):Prop:=
 let '((x,y),z):=j in exists Curve:secp_jacobian_curve x y (GZnZ.mul feP c z),
 secp_jacobian_group_value x y (GZnZ.mul feP c z) Curve=p.
Definition secp_jacobian_word_rep (c:secp_group_field)
 (j:Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) (p:secp_group_point):Prop:=
 secp_jacobian_context_rep c (secp_jacobian_word_fields j) p.
Local Opaque secp_field_word literal_gej_double_body literal_gej_double.
Lemma secp_literal_double_body_group (c:secp_group_field) (x y z:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c (@literal_gej_double_body Alg.CoreFunSem ((x,y),z))
 (SMain.add secp_group_theory p p).
Proof.
 intro Represented;destruct Represented as [Curve Value].
 unfold secp_jacobian_word_rep;rewrite secp_literal_double_body_fields.
 unfold secp_jacobian_context_rep.
 replace (GZnZ.mul feP c (GZnZ.mul feP (secp_field_word y) (secp_field_word z)))
 with (GZnZ.mul feP (secp_field_word y) (GZnZ.mul feP c (secp_field_word z))) by ring.
 exists (secp_jacobian_double_curve _ _ _ Curve).
 exact (eq_trans (secp_jacobian_double_group _ _ _ Curve)
  (f_equal2 (SMain.add secp_group_theory) Value Value)).
Qed.
Lemma secp_literal_infinity_fields:
 secp_jacobian_word_fields (@literal_gej_infinity Alg.CoreFunSem tt)=
 ((GZnZ.zero feP,GZnZ.zero feP),GZnZ.zero feP).
Proof.
 change (secp_jacobian_word_fields ((@Word.zero 8 Alg.CoreFunSem tt,@Word.zero 8 Alg.CoreFunSem tt),
  @Word.zero 8 Alg.CoreFunSem tt)=((GZnZ.zero feP,GZnZ.zero feP),GZnZ.zero feP)).
 unfold secp_jacobian_word_fields;cbn [fst snd];rewrite secp_field_word_zero;reflexivity.
Qed.
Lemma secp_literal_infinity_group c:
 secp_jacobian_word_rep c (@literal_gej_infinity Alg.CoreFunSem tt) secp_group_infinity.
Proof.
 unfold secp_jacobian_word_rep;rewrite secp_literal_infinity_fields.
 unfold secp_jacobian_context_rep.
 assert (Curve:secp_jacobian_curve (GZnZ.zero feP) (GZnZ.zero feP) (GZnZ.mul feP c (GZnZ.zero feP))).
 { unfold secp_jacobian_curve,secp_group_field;ring. }
 exists Curve;apply secp_jacobian_group_infinity_iff;unfold secp_group_field;ring.
Qed.
Lemma secp_literal_double_group (c:secp_group_field) (x y z:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c (@literal_gej_double Alg.CoreFunSem ((x,y),z))
 (SMain.add secp_group_theory p p).
Proof.
 intro Represented;rewrite literal_gej_double_step.
 destruct (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem ((x,y),z))) eqn:Flag.
 - assert (Zzero:secp_field_word z=GZnZ.zero feP).
   { apply (proj1 (SMain.is_zero_correct secp_group_theory (secp_field_word z))).
     rewrite secp_field_word_zero_test,<-(literal_gej_is_infinity_value x y z);exact Flag. }
   assert (Infinity:p=secp_group_infinity).
   { destruct Represented as [Curve Value].
     transitivity (secp_jacobian_group_value (secp_field_word x) (secp_field_word y)
      (GZnZ.mul feP c (secp_field_word z)) Curve).
     - symmetry;exact Value.
     - apply secp_jacobian_group_infinity_iff;rewrite Zzero;unfold secp_group_field;ring. }
   subst p;rewrite SMain.add_0_l;apply secp_literal_infinity_group.
 - apply secp_literal_double_body_group;exact Represented.
Qed.

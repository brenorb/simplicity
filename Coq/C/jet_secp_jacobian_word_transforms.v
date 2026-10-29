(** Group interpretation of the original literal Jacobian transforms:
    lambda, negate, rescale and zinv. Nonzero scales are internal premises to
    discharge from the table invariant. No public jet coverage is claimed. *)
From Coq Require Import ZArith Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_endomorphism C.jet_secp_curve_group_lambda
 C.jet_secp_jacobian_group C.jet_secp_jacobian_word_group C.jet_secp_field_word_group
 C.jet_secp_beta_global C.jet_secp_beta_spec C.jet_secp_table_get_lambda_literal
 C.jet_secp_canonical_normalize C.jet_secp_scalar_lambda_global C.jet_toZ.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_lambda_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Lemma secp_jacobian_curve_lambda (x y z:secp_group_field) (Curve:secp_jacobian_curve x y z):
 secp_jacobian_curve (GZnZ.mul feP secp_group_beta x) y z.
Proof.
 unfold secp_jacobian_curve in *;rewrite Curve,secp_group_beta_cube_scale;reflexivity.
Qed.
Lemma secp_jacobian_group_lambda (x y z:secp_group_field) (Curve:secp_jacobian_curve x y z):
 secp_jacobian_group_value (GZnZ.mul feP secp_group_beta x) y z (secp_jacobian_curve_lambda x y z Curve)=
 secp_group_endomorphism (secp_jacobian_group_value x y z Curve).
Proof.
 unfold secp_jacobian_group_value,secp_jacobian_projective,SMain.pe2e.
 destruct (SMain.wb (secp_group_zero_test (GZnZ.mul feP (GZnZ.mul feP z z) z))) as [b Test];destruct b;[reflexivity|].
 cbn [secp_group_endomorphism];apply (SMain.curve_elt_irr secp_group_theory);[|reflexivity].
 assert (Nonzero:z<>GZnZ.zero feP).
 { intro E;assert (Cube:GZnZ.mul feP (GZnZ.mul feP z z) z=GZnZ.zero feP)
    by (rewrite E;unfold secp_group_field;ring).
   pose proof (proj2 (SMain.is_zero_correct secp_group_theory _) Cube);congruence. }
 field;exact Nonzero.
Qed.
Lemma secp_field_integer_beta:secp_field_integer beta_value=secp_group_beta.
Proof.
 unfold secp_field_integer,secp_group_beta;apply GZnZ.zirr;apply Z.mod_small;exact (proj1 beta_value_range).
Qed.
Lemma secp_field_word_beta (x:Ty.tySem (Word 8)):
 secp_field_word (@literal_fe_multiply_beta Alg.CoreFunSem x)=GZnZ.mul feP secp_group_beta (secp_field_word x).
Proof.
 unfold secp_field_word;rewrite beta_literal_numeric,secp_field_integer_mod,secp_field_integer_mul,secp_field_integer_beta;reflexivity.
Qed.
Local Opaque secp_field_word literal_ge_scale_lambda.
Theorem secp_literal_scale_lambda_group (c:secp_group_field) (x y z:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c (@literal_ge_scale_lambda Alg.CoreFunSem (x,y),z)
 (EGroup.gpow p secp_curve_group canonical_lambda_value).
Proof.
 intro Represented;destruct Represented as [Curve Value].
 rewrite literal_ge_scale_lambda_step.
 unfold secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep;cbn [fst snd].
 rewrite secp_field_word_beta,secp_field_word_normalize.
 exists (secp_jacobian_curve_lambda _ _ _ Curve).
 transitivity (secp_group_endomorphism p).
 - exact (eq_trans (secp_jacobian_group_lambda _ _ _ Curve) (f_equal secp_group_endomorphism Value)).
 - apply secp_group_lambda_action.
Qed.
Require Import C.jet_secp_gej_negate_literal C.jet_secp_rescale_literal C.jet_secp_jacobian_mixed_word_group
 C.jet_secp_negate_literal_contract C.jet_secp_square_execution C.jet_secp_literal_add_program.
Lemma secp_literal_negate_group (c:secp_group_field) (x y z:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c (@literal_gej_negate Alg.CoreFunSem ((x,y),z)) (SMain.opp secp_group_theory p).
Proof.
 intro Represented;destruct Represented as [Curve Value].
 rewrite literal_gej_negate_step.
 unfold secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep;cbn [fst snd].
 rewrite !secp_field_word_normalize,secp_field_word_negate.
 exists (secp_jacobian_curve_negate _ _ _ Curve).
 exact (eq_trans (secp_jacobian_group_negate _ _ _ Curve) (f_equal (SMain.opp secp_group_theory) Value)).
Qed.
Lemma secp_literal_rescale_group (c:secp_group_field) (x y z s:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_field_word s<>GZnZ.zero feP ->secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c (@literal_gej_rescale Alg.CoreFunSem (((x,y),z),s)) p.
Proof.
 intros Nonzero Represented;destruct Represented as [Curve Value].
 rewrite literal_gej_rescale_step.
 unfold secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep;cbn [fst snd].
 rewrite !secp_field_word_mul,secp_field_word_square,secp_field_word_cube.
 replace (GZnZ.mul feP c (GZnZ.mul feP (secp_field_word z) (secp_field_word s)))
 with (GZnZ.mul feP (GZnZ.mul feP c (secp_field_word z)) (secp_field_word s)) by (unfold secp_group_field in *;ring).
 exists (secp_jacobian_curve_rescale _ _ _ Curve (secp_field_word s)).
 exact (eq_trans (secp_jacobian_group_rescale _ _ _ Curve (secp_field_word s) Nonzero) Value).
Qed.
Lemma secp_literal_zinv_step (x y s:Ty.tySem (Word 8)):
 @literal_gej_zinv Alg.CoreFunSem ((x,y),s)=
 (@literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem s),
  @literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_cube Alg.CoreFunSem s)).
Proof. reflexivity. Qed.
Lemma secp_literal_zinv_context_group (c:secp_group_field) (x y z s:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_field_word s<>GZnZ.zero feP ->secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep (GZnZ.mul feP (GZnZ.mul feP c (secp_field_word z)) (secp_field_word s))
 (@literal_gej_zinv Alg.CoreFunSem ((x,y),s),@literal_fe_one256 Alg.CoreFunSem tt) p.
Proof.
 intros Nonzero Represented;destruct Represented as [Curve Value].
 rewrite secp_literal_zinv_step.
 unfold secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep;cbn [fst snd].
 rewrite !secp_field_word_mul,secp_field_word_square,secp_field_word_cube,secp_field_word_one.
 replace (GZnZ.mul feP (GZnZ.mul feP (GZnZ.mul feP c (secp_field_word z)) (secp_field_word s)) (GZnZ.one feP))
 with (GZnZ.mul feP (GZnZ.mul feP c (secp_field_word z)) (secp_field_word s)) by (unfold secp_group_field in *;ring).
 exists (secp_jacobian_curve_rescale _ _ _ Curve (secp_field_word s)).
 exact (eq_trans (secp_jacobian_group_rescale _ _ _ Curve (secp_field_word s) Nonzero) Value).
Qed.

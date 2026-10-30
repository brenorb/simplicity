(** Scalar meaning of the checked four-stream group fold. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import SMain.
From Coqprime Require Import EGroup.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_power
 C.jet_secp_curve_group_endomorphism C.jet_secp_curve_group_lambda
 C.jet_secp_lookup5_group C.jet_secp_signed_group_action C.jet_secp_scalar_lambda_global
 C.jet_secp_canonical_scalar_lambda C.jet_secp_generate_small_group C.jet_secp_strauss_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque SMain.add SMain.opp EGroup.gpow secp_group_signed_power.
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Lemma secp_group_quad_interchange (a b c d:secp_group_point):
 (a⊕b)⊕(c⊕d)=(a⊕c)⊕(b⊕d).
Proof.
 rewrite <-!SMain.add_assoc;f_equal.
 rewrite (SMain.add_assoc secp_group_theory b c d),(SMain.add_comm secp_group_theory b c),<-SMain.add_assoc.
 reflexivity.
Qed.
Lemma secp_group_quad_sum (a b c d w x y z:secp_group_point):
 ((a⊕b)⊕(c⊕d))⊕((w⊕x)⊕(y⊕z))=((a⊕w)⊕(b⊕x))⊕((c⊕y)⊕(d⊕z)).
Proof.
 rewrite (secp_group_quad_interchange (a⊕b) (c⊕d) (w⊕x) (y⊕z)).
 rewrite (secp_group_quad_interchange a b w x),(secp_group_quad_interchange c d y z);reflexivity.
Qed.
Lemma secp_group_lambda_signed_point (p:secp_group_point) d:
 EGroup.gpow (secp_group_signed_power p d) secp_curve_group canonical_lambda_value=
 secp_group_signed_power (secp_group_endomorphism p) d.
Proof.
 transitivity (secp_group_signed_power (secp_group_signed_power p d) canonical_lambda_value).
 - symmetry;apply secp_group_signed_power_nonnegative;pose proof canonical_lambda_value_range;lia.
 - rewrite secp_group_signed_power_multiply,secp_group_signed_endo_action.
   f_equal;ring.
Qed.
Definition secp_strauss_coefficients:Set:=((Z*Z)*(Z*Z))%type.
Definition secp_strauss_coeff_add (c d:secp_strauss_coefficients):secp_strauss_coefficients:=
 ((fst (fst c)+fst (fst d),snd (fst c)+snd (fst d)),
  (fst (snd c)+fst (snd d),snd (snd c)+snd (snd d))).
Definition secp_strauss_combination (p:secp_group_point) (c:secp_strauss_coefficients):=
 (secp_group_signed_power p (fst (fst c))⊕
  secp_group_signed_power (secp_group_endomorphism p) (snd (fst c)))⊕
 (secp_group_signed_power secp_group_generator (fst (snd c))⊕
  secp_group_signed_power (EGroup.gpow secp_group_generator secp_curve_group (2^128)) (snd (snd c))).
Lemma secp_strauss_combination_add (p:secp_group_point) (c d:secp_strauss_coefficients):
 secp_strauss_combination p c⊕secp_strauss_combination p d=
 secp_strauss_combination p (secp_strauss_coeff_add c d).
Proof.
 destruct c as [[a b] [u v]],d as [[w x] [y z]].
 unfold secp_strauss_combination,secp_strauss_coeff_add;cbn [fst snd].
 rewrite secp_group_quad_sum;apply f_equal2.
 - apply f_equal2;symmetry;apply secp_group_signed_power_add.
 - apply f_equal2;symmetry;apply secp_group_signed_power_add.
Qed.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_generate_group C.jet_secp_strauss_program C.jet_secp_wnaf_literal
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_literal_array
 C.jet_secp_lookup5_literal.
Definition secp_strauss_digit_coefficients
 (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)):secp_strauss_coefficients:=
 ((wnaf5_literal_value (fst (fst ds)),wnaf5_literal_value (snd (fst ds))),
  (wnaf_literal_value (fst (snd ds)),wnaf_literal_value (snd (snd ds)))).
Theorem secp_strauss_group_step_linear (p a:secp_group_point)
 (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)):
 secp_strauss_group_digit_step p a ds=(a⊕a)⊕secp_strauss_combination p (secp_strauss_digit_coefficients ds).
Proof.
 destruct ds as [[d1 dl] [dg dh]].
 destruct d1 as [u1|n1],dl as [u2|n2],dg as [ug|ng],dh as [uh|nh];
 unfold secp_strauss_group_digit_step,secp_strauss_group_step,secp_strauss_combination,secp_strauss_digit_coefficients;
 cbn [fst snd wnaf5_literal_value wnaf_literal_value].
 all: repeat rewrite Z.mul_1_l.
 all: repeat rewrite secp_group_lambda_signed_point.
 all: repeat rewrite secp_generator_signed_zero.
 all: try rewrite <-(secp_generator_base_signed_action true _).
 all: repeat rewrite SMain.add_0_l.
 all: repeat rewrite SMain.add_0_r.
 all: repeat rewrite <-SMain.add_assoc.
 all: reflexivity.
Qed.
Definition secp_strauss_coefficient_step (c:secp_strauss_coefficients)
 (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)):=
 secp_strauss_coeff_add (secp_strauss_coeff_add c c) (secp_strauss_digit_coefficients ds).
Lemma secp_strauss_combination_step (p:secp_group_point) c ds:
 secp_strauss_group_digit_step p (secp_strauss_combination p c) ds=
 secp_strauss_combination p (secp_strauss_coefficient_step c ds).
Proof.
 unfold secp_strauss_coefficient_step.
 rewrite secp_strauss_group_step_linear,<-secp_strauss_combination_add,<-secp_strauss_combination_add;reflexivity.
Qed.
Lemma secp_strauss_combination_zero (p:secp_group_point):
 secp_strauss_combination p ((0,0),(0,0))=secp_group_infinity.
Proof.
 unfold secp_strauss_combination;cbn [fst snd];rewrite !secp_generator_signed_zero.
 apply SMain.add_0_l.
Qed.
From Coq Require Import List.
Import ListNotations.
Lemma secp_strauss_combination_fold (p:secp_group_point)
 (digits:list (Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))) c:
 fold_left (secp_strauss_group_digit_step p) digits (secp_strauss_combination p c)=
 secp_strauss_combination p (fold_left secp_strauss_coefficient_step digits c).
Proof.
 revert c;induction digits as [|digit digits IH];intro c;[reflexivity|].
 cbn [fold_left];rewrite secp_strauss_combination_step;apply IH.
Qed.
Lemma secp_strauss_group_fold_zero (p:secp_group_point)
 (digits:list (Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))):
 fold_left (secp_strauss_group_digit_step p) digits secp_group_infinity=
 secp_strauss_combination p (fold_left secp_strauss_coefficient_step digits ((0,0),(0,0))).
Proof. rewrite <-(secp_strauss_combination_zero p);apply secp_strauss_combination_fold. Qed.
Lemma secp_strauss_coefficient_horner a b c d ds:
 secp_strauss_coefficient_step ((a,b),(c,d)) ds=
 ((2*a+wnaf5_literal_value (fst (fst ds)),2*b+wnaf5_literal_value (snd (fst ds))),
  (2*c+wnaf_literal_value (fst (snd ds)),2*d+wnaf_literal_value (snd (snd ds)))).
Proof.
 unfold secp_strauss_coefficient_step,secp_strauss_coeff_add,secp_strauss_digit_coefficients;cbn [fst snd];f_equal;f_equal;ring.
Qed.
Theorem secp_strauss_coefficient_fold_values
 (digits:list (Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))) a b c d:
 fold_left secp_strauss_coefficient_step digits ((a,b),(c,d))=
 ((fold_left (fun acc ds=>2*acc+wnaf5_literal_value (fst (fst ds))) digits a,
   fold_left (fun acc ds=>2*acc+wnaf5_literal_value (snd (fst ds))) digits b),
  (fold_left (fun acc ds=>2*acc+wnaf_literal_value (fst (snd ds))) digits c,
   fold_left (fun acc ds=>2*acc+wnaf_literal_value (snd (snd ds))) digits d)).
Proof.
 revert a b c d;induction digits as [|digit digits IH];intros a b c d;[reflexivity|].
 cbn [fold_left];rewrite secp_strauss_coefficient_horner;apply IH.
Qed.
Require Import C.jet_secp_fe_math C.jet_secp_field_word_group C.jet_secp_jacobian_word_group
 C.jet_secp_table_pass2_group C.jet_secp_literal_infinity.
Theorem secp_literal_strauss_fold_scalar (z:Ty.tySem (Word 8))
 (table:Ty.tySem (C.jet_secp_scalar_table_literal.literal_table_vector 3)) (p:secp_group_point)
 (digits:list (Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))):
 secp_field_word z<>Coqprime.elliptic.GZnZ.zero feP ->
 secp_table_vector_group 3 table (secp_group_odd_table p) (secp_field_word z) ->
 Forall secp_strauss_group_digit_valid digits ->
 secp_jacobian_word_rep (secp_field_word z)
 (fold_left (fun point ds=>@literal_strauss_step Alg.CoreFunSem (point,((z,table),ds)))
  digits (@literal_gej_infinity Alg.CoreFunSem tt))
 (secp_strauss_combination p (fold_left secp_strauss_coefficient_step digits ((0,0),(0,0)))).
Proof.
 intros Nonzero Table Valid.
 rewrite <-secp_strauss_group_fold_zero.
 apply secp_literal_strauss_fold_group;[exact Nonzero|exact Table|exact Valid|apply secp_literal_infinity_group].
Qed.

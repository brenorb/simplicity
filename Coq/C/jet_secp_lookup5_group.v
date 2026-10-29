(** Signed lookup preserves the group interpretation of the original table. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_jacobian_group C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group
 C.jet_secp_field_word_group C.jet_secp_lookup5_literal C.jet_secp_gej_negate_literal
 C.jet_secp_wnaf5_literal_next C.jet_secp_scalar_table_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_field_word SMain.add SMain.opp EGroup.gpow literal_ge_negate literal_lookup5.
Definition secp_group_signed_power (p:secp_group_point) (k:Z):=
 if k <? 0 then SMain.opp secp_group_theory (EGroup.gpow p secp_curve_group (-k))
 else EGroup.gpow p secp_curve_group k.
Lemma secp_affine_negate_group (c:secp_group_field) (a:Ty.tySem literal_table_ge) (p:secp_group_point):
 secp_affine_word_rep c a p ->
 secp_affine_word_rep c (@literal_ge_negate Alg.CoreFunSem a) (SMain.opp secp_group_theory p).
Proof.
 Local Transparent literal_ge_negate.
 destruct a as [x y];intros [Curve Value].
 change (secp_affine_word_rep c
  (@C.jet_secp_canonical_normalize.canonical_fe_normalize Alg.CoreFunSem x,
   @C.jet_secp_negate_literal_contract.literal_fe_negate Alg.CoreFunSem y)
  (SMain.opp secp_group_theory p)).
 unfold secp_affine_word_rep,secp_jacobian_word_rep,secp_jacobian_word_fields,
  secp_jacobian_context_rep;cbn [fst snd].
 rewrite secp_field_word_normalize,secp_field_word_negate.
 exists (secp_jacobian_curve_negate _ _ _ Curve).
 exact (eq_trans (secp_jacobian_group_negate _ _ _ Curve)
  (f_equal (SMain.opp secp_group_theory) Value)).
Qed.
Local Opaque literal_ge_negate.
Definition secp_group_odd_table (p:secp_group_point):secp_group_vector 3:=
 (((EGroup.gpow p secp_curve_group 1,EGroup.gpow p secp_curve_group 3),
   (EGroup.gpow p secp_curve_group 5,EGroup.gpow p secp_curve_group 7)),
  ((EGroup.gpow p secp_curve_group 9,EGroup.gpow p secp_curve_group 11),
   (EGroup.gpow p secp_curve_group 13,EGroup.gpow p secp_curve_group 15))).
Theorem secp_literal_lookup5_group (c:secp_group_field)
 (table:Ty.tySem (literal_table_vector 3)) (p:secp_group_point) (nib:Ty.tySem (Word 2)):
 secp_table_vector_group 3 table (secp_group_odd_table p) c ->
 secp_affine_word_rep c (@literal_lookup5 Alg.CoreFunSem (nib,table))
  (secp_group_signed_power p (lookup5_digit nib)).
Proof.
 destruct table as [[[a1 a3] [a5 a7]] [[a9 a11] [a13 a15]]].
 intros [[[P1 P3] [P5 P7]] [[P9 P11] [P13 P15]]].
 destruct nib as [[b3 b2] [b1 b0]];
 destruct b3 as [u3|u3];destruct u3;destruct b2 as [u2|u2];destruct u2;
 destruct b1 as [u1|u1];destruct u1;destruct b0 as [u0|u0];destruct u0.
 all: match goal with
 | |- secp_affine_word_rep ?ctx ?a (secp_group_signed_power ?point ?k)=>
   let digit:=eval vm_compute in k in
   change (secp_affine_word_rep ctx a (secp_group_signed_power point digit))
 end.
 all: lazymatch goal with
 | |- secp_affine_word_rep _ _ (secp_group_signed_power _ ?k)=>
   lazymatch k with
   | 1 => exact P1
   | 3 => exact P3
   | 5 => exact P5
   | 7 => exact P7
   | 9 => exact P9
   | 11 => exact P11
   | 13 => exact P13
   | 15 => exact P15
   | -1 => exact (secp_affine_negate_group c a1 _ P1)
   | -3 => exact (secp_affine_negate_group c a3 _ P3)
   | -5 => exact (secp_affine_negate_group c a5 _ P5)
   | -7 => exact (secp_affine_negate_group c a7 _ P7)
   | -9 => exact (secp_affine_negate_group c a9 _ P9)
   | -11 => exact (secp_affine_negate_group c a11 _ P11)
   | -13 => exact (secp_affine_negate_group c a13 _ P13)
   | -15 => exact (secp_affine_negate_group c a15 _ P15)
   end
 end.
Qed.
Require Import C.jet_secp_scalar_table_group C.jet_secp_jacobian_word_transforms
 C.jet_secp_table_get_lambda_literal C.jet_secp_scalar_lambda_global C.jet_secp_curve_literal.
Theorem secp_literal_scalar_table_lookup5_group (ax ay:Ty.tySem (Word 8))
 (p:secp_group_point) (nib:Ty.tySem (Word 2)):
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 secp_jacobian_word_rep (GZnZ.one feP) ((ax,ay),@C.jet_secp_literal_add_program.literal_fe_one256 Alg.CoreFunSem tt) p ->
 let result:=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),@C.jet_secp_literal_add_program.literal_fe_one256 Alg.CoreFunSem tt) in
 secp_affine_word_rep (secp_field_word (fst result))
  (@literal_lookup5 Alg.CoreFunSem (nib,snd result))
  (secp_group_signed_power p (lookup5_digit nib)).
Proof.
 intros Valid Represented;cbn zeta.
 destruct (secp_literal_scalar_table5_group ax ay p Valid Represented) as [Nonzero Table].
 apply secp_literal_lookup5_group;exact Table.
Qed.
Theorem secp_literal_lookup5_lambda_group (c:secp_group_field)
 (table:Ty.tySem (literal_table_vector 3)) (p:secp_group_point) (nib:Ty.tySem (Word 2)):
 secp_table_vector_group 3 table (secp_group_odd_table p) c ->
 secp_affine_word_rep c
  (@literal_ge_scale_lambda Alg.CoreFunSem (@literal_lookup5 Alg.CoreFunSem (nib,table)))
  (EGroup.gpow (secp_group_signed_power p (lookup5_digit nib)) secp_curve_group canonical_lambda_value).
Proof.
 intro Table;pose proof (secp_literal_lookup5_group c table p nib Table) as Looked.
 destruct (@literal_lookup5 Alg.CoreFunSem (nib,table)) as [x y].
 exact (secp_literal_scale_lambda_group c x y
  (@C.jet_secp_literal_add_program.literal_fe_one256 Alg.CoreFunSem tt) _ Looked).
Qed.

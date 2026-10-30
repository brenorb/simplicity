(** The canonical subtraction/infinity predicate is group equality. *)
From Coq Require Import ZArith Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_curve_group_sign C.jet_secp_curve_group_power C.jet_secp_field_word_group
 C.jet_secp_jacobian_group C.jet_secp_jacobian_word_group C.jet_secp_jacobian_mixed_word_group
 C.jet_secp_table_pass2_group C.jet_secp_lookup5_group C.jet_secp_strauss_group
 C.jet_secp_linear_combination_group C.jet_secp_linear_verify_literal
 C.jet_secp_literal_gej_predicate C.jet_secp_literal_add_program C.jet_secp_scalar_table_literal
 C.jet_secp_strauss_complete_program C.jet_secp_canonical_scalar C.jet_secp_curve_literal
 C.jet_secp_gej_negate_literal C.jet_secp_add_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_linear_check_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Local Opaque literal_gej_is_infinity literal_off_curve_linear_combination_1
 literal_gej_ge_add literal_ge_negate secp_field_word secp_group_signed_power SMain.add SMain.opp.
Lemma secp_jacobian_word_infinity (point:Ty.tySem literal_table_gej) (p:secp_group_point):
 secp_jacobian_word_rep (GZnZ.one feP) point p ->
 (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point)=Datatypes.true <->p=secp_group_infinity).
Proof.
 destruct point as [[x y] z];intros [Curve Value].
 cbn [secp_jacobian_word_fields fst snd] in Curve,Value.
 rewrite literal_gej_is_infinity_value,secp_field_word_flag_true,<-Value.
 rewrite secp_jacobian_group_infinity_iff.
 assert (Unit:forall t:secp_group_field,GZnZ.mul feP (GZnZ.one feP) t=t).
 { intro t;unfold secp_group_field in *;ring. }
 rewrite Unit;reflexivity.
Qed.
Lemma secp_group_subtract_infinity (p q:secp_group_point):
 p⊕SMain.opp secp_group_theory q=secp_group_infinity <->p=q.
Proof.
 split.
 - intro Equal;pose proof (SMain.uniq_opp secp_group_theory p (SMain.opp secp_group_theory q) Equal) as Opposite.
   pose proof (f_equal (SMain.opp secp_group_theory) Opposite) as Same.
   rewrite !SMain.opp_opp in Same;symmetry;exact Same.
 - intro Equal;subst q;apply SMain.add_opp.
Qed.
Theorem secp_literal_linear_check_group (raw ng ax ay bx byword:Ty.tySem (Word 8)) (p q:secp_group_point):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bx,byword))=Datatypes.true ->
 secp_affine_word_rep (GZnZ.one feP) (ax,ay) p ->secp_affine_word_rep (GZnZ.one feP) (bx,byword) q ->
 (Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bx,byword)))=Datatypes.true <->
 secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))⊕
 secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))=q).
Proof.
 intros ValidP ValidQ RepP RepQ.
 pose proof (secp_literal_linear_combination_affine_group raw ng ax ay p ValidP RepP) as Combined.
 pose proof (secp_affine_negate_group (GZnZ.one feP) (bx,byword) q RepQ) as Negated.
 pose proof (secp_literal_mixed_group_output (GZnZ.one feP) _ _ _ _
  (SMain.one_not_zero secp_group_theory) Combined Negated) as Difference.
 rewrite literal_linear_check_value,ValidQ,ValidP;cbn [andb].
 rewrite (secp_jacobian_word_infinity _ _ Difference);apply secp_group_subtract_infinity.
Qed.

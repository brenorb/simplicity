(** Full affine routing, including the original generator-only branch. *)
From Coq Require Import ZArith.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_field_word_group C.jet_secp_jacobian_word_group
 C.jet_secp_lookup5_group C.jet_secp_generate_group C.jet_secp_signed_group_action
 C.jet_secp_generate_program C.jet_secp_strauss_body_group C.jet_secp_generator_complete_group
 C.jet_secp_strauss_complete_program C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_zero
 C.jet_secp_literal_add_program C.jet_secp_literal_gej_predicate C.jet_secp_negate_literal_contract C.jet_secp_curve_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_off_curve_linear_combination_1 literal_strauss_body
 literal_generate canonical_scalar_normalize canonical_scalar_is_zero literal_gej_is_infinity
 secp_field_word SMain.add secp_group_signed_power.
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Lemma secp_literal_affine_strauss_guard (raw ng ax ay:Ty.tySem (Word 8)):
 Bit.toBool (@literal_strauss_guard Alg.CoreFunSem ((raw,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),ng))=
 Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem raw).
Proof.
 rewrite literal_strauss_guard_value,literal_gej_is_infinity_value,<-secp_field_word_zero_test,secp_field_word_one.
 reflexivity.
Qed.
Theorem secp_literal_linear_combination_affine_group (raw ng ax ay:Ty.tySem (Word 8)) (p:secp_group_point):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 secp_jacobian_word_rep (GZnZ.one feP) ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) p ->
 secp_jacobian_word_rep (GZnZ.one feP)
 (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
  ((raw,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),ng))
 (secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))⊕
  secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))).
Proof.
 intros Valid Represented;rewrite literal_off_curve_linear_combination_1_value,secp_literal_affine_strauss_guard.
 destruct (Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem raw)) eqn:Zero.
 - assert (Normalized:@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)=0).
   { apply Z.eqb_eq;rewrite canonical_scalar_zero_after_normalize;exact Zero. }
   rewrite Normalized,secp_generator_signed_zero,SMain.add_0_l.
   apply secp_literal_generate_group.
 - apply secp_literal_strauss_body_affine_group;assumption.
Qed.

(** Literal linear_check_1 / linear_verify_1 from the frozen
    LibSecp256k1.hs:667--671,823--824. This adapter preserves both curve
    guards, affine Z=1 routing, negation, mixed addition and infinity test.
    It is a specification bridge, not a public C execution proof. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Import C.jet_secp_strauss_complete_program C.jet_secp_strauss_parametric
 C.jet_secp_scalar_table_literal C.jet_secp_curve_literal C.jet_secp_add_literal
 C.jet_secp_literal_gej_predicate C.jet_secp_gej_negate_literal
 C.jet_secp_gej_negate_parametric C.jet_secp_literal_add_program C.jet_assertion_spec.
Local Open Scope term_scope.
Set Default Timeout 10.
Module SC := Alg.Core.Combinators.

Definition literal_linear_verify_args :=
 Ty.Prod (Ty.Prod (Ty.Prod (Word 8) literal_table_ge) (Word 8)) literal_table_ge.

Definition literal_affine_linear_routing {term:Alg.Core.Algebra} :
 term (Ty.Prod (Ty.Prod (Word 8) literal_table_ge) (Word 8)) literal_strauss_args :=
 O (O H &&& (I H &&& (unit >>> @literal_fe_one256 term))) &&& I H.

Definition literal_linear_check_body {term:Alg.Core.Algebra} :
 term literal_linear_verify_args Bit :=
 ((O (@literal_affine_linear_routing term >>> @literal_off_curve_linear_combination_1 term))
  &&& I (@literal_ge_negate term)) >>> @literal_gej_ge_add term >>> @literal_gej_is_infinity term.

Definition literal_linear_check {term:Alg.Core.Algebra} : term literal_linear_verify_args Bit :=
 Bit.and (I (@literal_ge_is_on_curve term))
  (Bit.and (O (O (I (@literal_ge_is_on_curve term)))) (@literal_linear_check_body term)).

Lemma literal_linear_check_parametric : Alg.Core.Parametric (@literal_linear_check).
Proof.
 intros a b R;unfold literal_linear_check,literal_linear_check_body,literal_affine_linear_routing.
 repeat first [apply Bit.and_Parametric|apply literal_ge_is_on_curve_parametric|
  apply scale_off_curve_combination_parametric|apply literal_ge_negate_parametric|
  apply literal_gej_ge_add_parametric|apply literal_gej_is_infinity_parametric|
  apply literal_fe_one256_parametric|apply Alg.comp_Parametric|apply Alg.pair_Parametric|
  apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric|apply Alg.unit_Parametric].
Qed.

Definition literal_linear_verify {term:Alg.Assertion.Algebra} : term literal_linear_verify_args Ty.Unit :=
 SC.comp (SC.pair (@literal_linear_check (Alg.Assertion.toCore term)) SC.unit)
  (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.take SC.iden)).

Lemma literal_linear_verify_parametric : Alg.Assertion.Parametric (@literal_linear_verify).
Proof.
 intros a b [R [HC HA]];unfold literal_linear_verify.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC)).
   + apply (literal_linear_check_parametric _ _ (Alg.Core.Parametric.Pack HC)).
   + apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC));apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC)).
Qed.

Local Opaque literal_ge_is_on_curve literal_ge_negate literal_gej_ge_add
 literal_gej_is_infinity literal_fe_one256 literal_off_curve_linear_combination_1.

Lemma literal_linear_check_value (na ng:Ty.tySem (Word 8))
 (a b:Ty.tySem literal_table_ge) :
 Bit.toBool (@literal_linear_check Alg.CoreFunSem (((na,a),ng),b))=
 andb (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem b))
  (andb (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem a))
   (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem
     (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
       ((na,(a,@literal_fe_one256 Alg.CoreFunSem tt)),ng),
      @literal_ge_negate Alg.CoreFunSem b))))).
Proof.
 unfold literal_linear_check,literal_linear_check_body,literal_affine_linear_routing.
 cbn -[literal_ge_is_on_curve literal_ge_negate literal_gej_ge_add
  literal_gej_is_infinity literal_fe_one256 literal_off_curve_linear_combination_1].
 destruct (@literal_ge_is_on_curve Alg.CoreFunSem b) as [u|u];destruct u;
 destruct (@literal_ge_is_on_curve Alg.CoreFunSem a) as [v|v];destruct v;reflexivity.
Qed.

Local Opaque literal_linear_check.
Lemma literal_linear_verify_option (input:Ty.tySem literal_linear_verify_args) :
 @literal_linear_verify (Alg.AssertionSem option_Monad_Zero) input=
 if Bit.toBool (@literal_linear_check Alg.CoreFunSem input) then Some tt else None.
Proof.
 pose proof (Alg.CoreSem_initial (M:=option_CIMonad) literal_linear_check_parametric input) as Core.
 change (@literal_linear_check (Alg.AssertionSem option_Monad_Zero) input=
  Some (@literal_linear_check Alg.CoreFunSem input)) in Core.
 unfold literal_linear_verify,SC.comp,SC.pair,SC.unit.
 cbn [Alg.Core.comp Alg.Core.pair Alg.Core.unit Alg.Core.class_of Alg.Assertion.toCore
   Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
   Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
   Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
   Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
   option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 lazymatch goal with |- context[@literal_linear_check ?alg input] =>
  assert (Lift:@literal_linear_check alg input=
   Some (@literal_linear_check Alg.CoreFunSem input)) by exact Core;
  rewrite Lift
 end.
 cbn [Monad.CIMonad.bind option_bind].
 destruct (@literal_linear_check Alg.CoreFunSem input) as [u|u];destruct u;reflexivity.
Qed.

Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Import C.jet_secp_strauss_parametric C.jet_secp_strauss_complete_program
 C.jet_secp_scalar_table_literal C.jet_secp_curve_literal C.jet_assertion_spec.
Local Open Scope term_scope.
Set Default Timeout 10.
Module SC := Alg.Core.Combinators.
Definition literal_checked_linear_core {term:Alg.Core.Algebra} :
 term literal_strauss_args (Ty.Prod Bit literal_table_gej) :=
 SC.pair (SC.take (SC.drop (@literal_gej_is_on_curve term))) (@literal_off_curve_linear_combination_1 term).
Lemma literal_checked_linear_core_parametric : Alg.Core.Parametric (@literal_checked_linear_core).
Proof.
 intros a b R;unfold literal_checked_linear_core.
 apply Alg.pair_Parametric.
 - apply Alg.take_Parametric;apply Alg.drop_Parametric;apply literal_gej_is_on_curve_parametric.
 - apply scale_off_curve_combination_parametric.
Qed.
Definition literal_checked_linear {term:Alg.Assertion.Algebra} :
 term literal_strauss_args literal_table_gej :=
 SC.comp (@literal_checked_linear_core (Alg.Assertion.toCore term))
  (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.drop SC.iden)).
Lemma literal_checked_linear_parametric : Alg.Assertion.Parametric (@literal_checked_linear).
Proof.
 intros a b [R [HC HA]];unfold literal_checked_linear.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (literal_checked_linear_core_parametric _ _ (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.assertr_Parametric
     (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   apply (Alg.drop_Parametric (Alg.Core.Parametric.Pack HC));apply Alg.iden_Parametric.
Qed.
Lemma literal_checked_linear_core_value raw point ng :
 @literal_checked_linear_core Alg.CoreFunSem ((raw,point),ng)=
 (@literal_gej_is_on_curve Alg.CoreFunSem point,@literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,point),ng)).
Proof. reflexivity. Qed.
Local Opaque literal_off_curve_linear_combination_1 literal_gej_is_on_curve literal_checked_linear_core.
Lemma literal_checked_linear_option raw point ng :
 @literal_checked_linear (Alg.AssertionSem option_Monad_Zero) ((raw,point),ng)=
 if Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem point)
 then Some (@literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,point),ng)) else None.
Proof.
 pose proof (Alg.CoreSem_initial (M:=option_CIMonad) literal_checked_linear_core_parametric ((raw,point),ng)) as Core.
 change (@literal_checked_linear_core (Alg.AssertionSem option_Monad_Zero) ((raw,point),ng)=
  Some (@literal_checked_linear_core Alg.CoreFunSem ((raw,point),ng))) in Core.
 unfold literal_checked_linear,SC.comp.
 cbn [Alg.Core.comp Alg.Core.class_of Alg.Assertion.toCore
   Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
   Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
   Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
   Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
   option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 match goal with |-context[@literal_checked_linear_core ?alg ((raw,point),ng)]=>
   assert (Lift:@literal_checked_linear_core alg ((raw,point),ng)=
     Some (@literal_checked_linear_core Alg.CoreFunSem ((raw,point),ng))) by exact Core;
   lazymatch goal with |- ?f ?x = _ =>
     eapply eq_trans;[exact (f_equal f Lift)|]
   end
 end.
 rewrite literal_checked_linear_core_value.
 cbn [Monad.CIMonad.bind option_bind literal_checked_linear_core SC.pair SC.drop SC.iden
  Alg.Core.pair Alg.Core.drop Alg.Core.iden Alg.Core.class_of Alg.CoreFunSem
  Alg.CoreSem Alg.CoreSem_mixin].
 change ((match @literal_gej_is_on_curve Alg.CoreFunSem point with
  | inl _=>None|inr _=>Some (@literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,point),ng)) end)=
  if Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem point)
  then Some (@literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,point),ng)) else None).
 destruct (@literal_gej_is_on_curve Alg.CoreFunSem point);reflexivity.
Qed.


(** Faithful point_check_1 / point_verify_1 port from the frozen
    LibSecp256k1.hs:680--686,826--827. The public execution proof is separate. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Import C.jet_secp_linear_verify_literal C.jet_secp_decompress_literal C.jet_assertion_spec.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_compressed_point := Ty.Prod Bit (Word 8).
Definition literal_point_verify_args :=
 Ty.Prod (Ty.Prod (Ty.Prod (Word 8) literal_compressed_point) (Word 8)) literal_compressed_point.

Definition literal_point_check_k2 {term:Alg.Core.Algebra} :
 term (Ty.Prod (Ty.Prod (Word 8) (Word 8))
   (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8)))) Bit :=
 ((I (O (O H)) &&& O H) &&& I (O (I H))) &&& I (I H) >>> @literal_linear_check term.

Definition literal_point_check_k1 {term:Alg.Core.Algebra} :
 term (Ty.Prod (Ty.Prod (Word 8) (Word 8))
   (Ty.Prod (Ty.Prod (Word 8) literal_compressed_point) (Word 8))) Bit :=
 (I (O (I (@literal_decompress term))) &&& (I (O (O H) &&& I H) &&& O H))
 >>> case Bit.false (@literal_point_check_k2 term).

Definition literal_point_check {term:Alg.Core.Algebra} : term literal_point_verify_args Bit :=
 I (@literal_decompress term) &&& O H >>> case Bit.false (@literal_point_check_k1 term).

Lemma literal_point_check_parametric : Alg.Core.Parametric (@literal_point_check).
Proof.
 intros a b R;unfold literal_point_check,literal_point_check_k1,literal_point_check_k2.
 repeat first [apply literal_decompress_parametric|apply literal_linear_check_parametric|
  apply Bit.false_Parametric|apply Alg.comp_Parametric|apply Alg.pair_Parametric|
  apply Alg.case_Parametric|apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.

Definition literal_point_verify {term:Alg.Assertion.Algebra} : term literal_point_verify_args Ty.Unit :=
 SC.comp (SC.pair (@literal_point_check (Alg.Assertion.toCore term)) SC.unit)
  (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.take SC.iden)).

Lemma literal_point_verify_parametric : Alg.Assertion.Parametric (@literal_point_verify).
Proof.
 intros a b [R [HC HA]];unfold literal_point_verify.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC)).
   + apply (literal_point_check_parametric _ _ (Alg.Core.Parametric.Pack HC)).
   + apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC));apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC)).
Qed.

Local Opaque literal_decompress literal_linear_check.
Lemma literal_point_check_value (na ng:Ty.tySem (Word 8))
 (a b:Ty.tySem literal_compressed_point) :
 @literal_point_check Alg.CoreFunSem (((na,a),ng),b)=
 match @literal_decompress Alg.CoreFunSem b with
 | inl _ => inl tt
 | inr bp => match @literal_decompress Alg.CoreFunSem a with
   | inl _ => inl tt
   | inr ap => @literal_linear_check Alg.CoreFunSem (((na,ap),ng),bp)
   end
 end.
Proof.
 unfold literal_point_check,literal_point_check_k1,literal_point_check_k2.
 cbn -[literal_decompress literal_linear_check].
 destruct (@literal_decompress Alg.CoreFunSem b) as [u|bp];[destruct u;reflexivity|].
 destruct (@literal_decompress Alg.CoreFunSem a) as [u|ap];[destruct u;reflexivity|reflexivity].
Qed.

Local Opaque literal_point_check.
Lemma literal_point_verify_option (input:Ty.tySem literal_point_verify_args) :
 @literal_point_verify (Alg.AssertionSem option_Monad_Zero) input=
 if Bit.toBool (@literal_point_check Alg.CoreFunSem input) then Some tt else None.
Proof.
 pose proof (Alg.CoreSem_initial (M:=option_CIMonad) literal_point_check_parametric input) as Core.
 change (@literal_point_check (Alg.AssertionSem option_Monad_Zero) input=
  Some (@literal_point_check Alg.CoreFunSem input)) in Core.
 unfold literal_point_verify,SC.comp,SC.pair,SC.unit.
 cbn [Alg.Core.comp Alg.Core.pair Alg.Core.unit Alg.Core.class_of Alg.Assertion.toCore
   Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
   Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
   Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
   Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
   option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 lazymatch goal with |- context[@literal_point_check ?alg input] =>
  assert (Lift:@literal_point_check alg input=
   Some (@literal_point_check Alg.CoreFunSem input)) by exact Core;
  rewrite Lift
 end.
 cbn [Monad.CIMonad.bind option_bind].
 destruct (@literal_point_check Alg.CoreFunSem input) as [u|u];destruct u;reflexivity.
Qed.

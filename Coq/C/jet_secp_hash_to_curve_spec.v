(** Exact outer assert from LibSecp256k1.hs:837 and Programs/Bit.hs:49--50.
    Keep the canonical pruned-branch hash and reuse the checked core program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_assertion_spec C.jet_secp_hash_public_literal
 C.jet_secp_hash_public_call C.jet_secp_generator_hash_map C.jet_secp_rescale_literal.
Module AC := Alg.Core.Combinators.
Set Default Timeout 10.
Local Opaque literal_hash_to_curve_core rescale_field_output.

Definition literal_hash_to_curve {term:Alg.Assertion.Algebra} :
 term (Word 8) (Ty.Prod (Word 8) (Word 8)) :=
 AC.comp (AC.pair (@literal_hash_to_curve_core (Alg.Assertion.toCore term)) AC.unit)
   (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (AC.take AC.iden)).

Lemma literal_hash_to_curve_parametric : Alg.Assertion.Parametric (@literal_hash_to_curve).
Proof.
 intros alg1 alg2 [R [HC HA]];unfold literal_hash_to_curve.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC)).
   + apply (literal_hash_to_curve_core_parametric _ _ (Alg.Core.Parametric.Pack HC)).
   + apply Alg.unit_Parametric.
 - apply (Alg.assertr_Parametric
     (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC));apply Alg.iden_Parametric.
Qed.

Lemma literal_hash_to_curve_option key :
 @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key=
 match @literal_hash_to_curve_core Alg.CoreFunSem key with inl _=>None | inr p=>Some p end.
Proof.
 pose proof (Alg.CoreSem_initial (M:=option_CIMonad) literal_hash_to_curve_core_parametric key) as Core.
 change (@literal_hash_to_curve_core (Alg.AssertionSem option_Monad_Zero) key=
   Some (@literal_hash_to_curve_core Alg.CoreFunSem key)) in Core.
 unfold literal_hash_to_curve,AC.comp,AC.pair.
 cbn [Alg.Core.comp Alg.Core.pair Alg.Core.class_of Alg.Assertion.toCore
   Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
   Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
   Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
   Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
   option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 match goal with |-context[@literal_hash_to_curve_core ?alg key]=>
   replace (@literal_hash_to_curve_core alg key) with
     (Some (@literal_hash_to_curve_core Alg.CoreFunSem key)) by (symmetry;exact Core)
 end;reflexivity.
Qed.

Theorem hash_public_assertion_result key sx sy sz flag ox oy :
 hash_public_value key sx sy sz flag ox oy ->
 @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key=
 if andb (generator_hash_accepted Datatypes.false key) (generator_hash_accepted Datatypes.true key)
 then if Int.eq flag Int.zero then Some (rescale_field_output ox,rescale_field_output oy) else None
 else None.
Proof.
 intro Value;rewrite literal_hash_to_curve_option,(hash_public_core_result _ _ _ _ _ _ _ Value).
 destruct (andb (generator_hash_accepted Datatypes.false key) (generator_hash_accepted Datatypes.true key));
   [destruct (Int.eq flag Int.zero)|];reflexivity.
Qed.

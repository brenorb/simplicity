(** Literal frozen LibSecp256k1 pubkey_unpack_neg, signature_unpack and
    bip_0340_check (lines 690--707). This port does not claim public C execution. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import Simplicity.Util.Option C.jet_assertion_spec.
Require Import C.jet_order_spec C.jet_secp_canonical_normalize C.jet_secp_canonical_scalar
 C.jet_secp_point_verify_literal C.jet_secp_schnorr_challenge_literal
 C.jet_secp_schnorr_challenge_hash.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Module SC:=Alg.Core.Combinators.
Definition literal_schnorr_signature:=Ty.Prod (Word 8) (Word 8).
Definition literal_schnorr_pubkey_check {term:Alg.Core.Algebra}:
 term (Word 8) (Ty.Prod Bit (Word 8)) :=
 ((iden &&& Alg.scribe canonical_field_word) >>> @lt_word_spec term 8) &&& iden.
Definition literal_schnorr_pubkey_unpack_neg {term:Alg.Core.Algebra}:
 term (Word 8) (Ty.Sum Ty.Unit literal_compressed_point) :=
 @literal_schnorr_pubkey_check term >>> Bit.cond
  (injr ((unit >>> Bit.true) &&& iden)) (injl unit).
Definition literal_schnorr_signature_unpack {term:Alg.Core.Algebra}:
 term literal_schnorr_signature (Ty.Sum Ty.Unit literal_schnorr_signature) :=
 (Bit.and ((O H &&& Alg.scribe canonical_field_word) >>> @lt_word_spec term 8)
          ((I H &&& Alg.scribe canonical_group_word) >>> @lt_word_spec term 8) &&& iden)
 >>> Bit.cond (injr iden) (injl unit).
Definition literal_bip0340_k2 {term:Alg.Core.Algebra}:
 term (Ty.Prod literal_schnorr_signature (Ty.Prod (Word 8) literal_compressed_point)) Bit :=
 ((I H &&& O (I H)) &&& ((unit >>> Bit.false) &&& O (O H))) >>> @literal_point_check term.
Definition literal_bip0340_k1 {term:Alg.Core.Algebra}:
 term (Ty.Prod literal_compressed_point
  (Ty.Prod (Word 8) (Ty.Sum Ty.Unit literal_schnorr_signature))) Bit :=
 (I (I H) &&& (I (O H) &&& O H)) >>> case Bit.false (@literal_bip0340_k2 term).
Definition literal_bip0340_check {term:Alg.Core.Algebra}:term literal_bip0340_args Bit :=
 (O (O (@literal_schnorr_pubkey_unpack_neg term)) &&&
  (@literal_bip0340_challenge term &&& I (@literal_schnorr_signature_unpack term)))
 >>> case Bit.false (@literal_bip0340_k1 term).
Local Ltac schnorr_parametric:=repeat first [
 apply literal_bip0340_challenge_parametric|apply literal_point_check_parametric|
 apply lt_word_spec_parametric|apply Bit.and_Parametric|apply Bit.cond_Parametric|
 apply Bit.false_Parametric|apply Bit.true_Parametric|apply Alg.scribe_Parametric|
 apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.take_Parametric|
 apply Alg.drop_Parametric|apply Alg.case_Parametric|apply Alg.injl_Parametric|
 apply Alg.injr_Parametric|apply Alg.iden_Parametric|apply Alg.unit_Parametric].
Lemma literal_bip0340_check_parametric:Alg.Core.Parametric (@literal_bip0340_check).
Proof.
 intros a b R;unfold literal_bip0340_check,literal_bip0340_k1,literal_bip0340_k2,
 literal_schnorr_pubkey_unpack_neg,literal_schnorr_pubkey_check,literal_schnorr_signature_unpack.
 schnorr_parametric.
Qed.
Local Opaque lt_word_spec canonical_field_word canonical_group_word literal_point_check
 literal_bip0340_challenge literal_schnorr_pubkey_unpack_neg literal_schnorr_signature_unpack.
Lemma literal_bip0340_check_value (pk msg r s:Ty.tySem (Word 8)):
 @literal_bip0340_check Alg.CoreFunSem ((pk,msg),(r,s))=
 match @literal_schnorr_pubkey_unpack_neg Alg.CoreFunSem pk with
 | inl _=>inl tt
 | inr point=>match @literal_schnorr_signature_unpack Alg.CoreFunSem (r,s) with
   | inl _=>inl tt
   | inr rs=>@literal_point_check Alg.CoreFunSem
      (((@literal_bip0340_challenge Alg.CoreFunSem ((pk,msg),(r,s)),point),snd rs),
       (inl tt,fst rs))
   end
 end.
Proof.
 unfold literal_bip0340_check,literal_bip0340_k1,literal_bip0340_k2.
 cbn -[literal_schnorr_pubkey_unpack_neg literal_schnorr_signature_unpack literal_bip0340_challenge literal_point_check].
 destruct (@literal_schnorr_pubkey_unpack_neg Alg.CoreFunSem pk) as [u|point];[destruct u;reflexivity|].
 destruct (@literal_schnorr_signature_unpack Alg.CoreFunSem (r,s)) as [u|rs];[destruct u;reflexivity|reflexivity].
Qed.

Definition literal_bip0340_verify {term:Alg.Assertion.Algebra} : term literal_bip0340_args Ty.Unit :=
 SC.comp (SC.pair (@literal_bip0340_check (Alg.Assertion.toCore term)) SC.unit)
  (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.take SC.iden)).

Lemma literal_bip0340_verify_parametric : Alg.Assertion.Parametric (@literal_bip0340_verify).
Proof.
 intros a b [R [HC HA]];unfold literal_bip0340_verify.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC)).
   + apply (literal_bip0340_check_parametric _ _ (Alg.Core.Parametric.Pack HC)).
   + apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC));apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC)).
Qed.


Local Opaque literal_bip0340_check.
Lemma literal_bip0340_verify_option (input:Ty.tySem literal_bip0340_args) :
 @literal_bip0340_verify (Alg.AssertionSem option_Monad_Zero) input=
 if Bit.toBool (@literal_bip0340_check Alg.CoreFunSem input) then Some tt else None.
Proof.
 pose proof (Alg.CoreSem_initial (M:=option_CIMonad) literal_bip0340_check_parametric input) as Core.
 change (@literal_bip0340_check (Alg.AssertionSem option_Monad_Zero) input=
  Some (@literal_bip0340_check Alg.CoreFunSem input)) in Core.
 unfold literal_bip0340_verify,SC.comp,SC.pair,SC.unit.
 cbn [Alg.Core.comp Alg.Core.pair Alg.Core.unit Alg.Core.class_of Alg.Assertion.toCore
   Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
   Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
   Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
   Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
   option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 lazymatch goal with |- context[@literal_bip0340_check ?alg input] =>
  assert (Lift:@literal_bip0340_check alg input=
   Some (@literal_bip0340_check Alg.CoreFunSem input)) by exact Core;
  rewrite Lift
 end.
 cbn [Monad.CIMonad.bind option_bind].
 destruct (@literal_bip0340_check Alg.CoreFunSem input) as [u|u];destruct u;reflexivity.
Qed.

Local Transparent literal_schnorr_pubkey_unpack_neg literal_schnorr_signature_unpack.
Lemma literal_schnorr_pubkey_unpack_neg_value (pk:Ty.tySem (Word 8)):
 @literal_schnorr_pubkey_unpack_neg Alg.CoreFunSem pk=
 if @toZ (WordToZ 8) pk <? canonical_field_order then inr (inr tt,pk) else inl tt.
Proof.
 pose proof (lt_word_spec_numeric 8 pk canonical_field_word) as Compare.
 rewrite canonical_field_word_value in Compare.
 rewrite <-Compare.
 unfold literal_schnorr_pubkey_unpack_neg,literal_schnorr_pubkey_check.
 cbn -[lt_word_spec Alg.scribe canonical_field_word canonical_group_word].
 rewrite Alg.scribe_correct.
 change ((match @lt_word_spec Alg.CoreFunSem 8 (pk,canonical_field_word) with
   | inl _=>inl tt|inr _=>inr (inr tt,pk) end :Ty.tySem (Ty.Sum Ty.Unit literal_compressed_point))=
   if Bit.toBool (@lt_word_spec Alg.CoreFunSem 8 (pk,canonical_field_word))
   then inr (inr tt,pk) else inl tt).
 destruct (@lt_word_spec Alg.CoreFunSem 8 (pk,canonical_field_word)) as [u|u];destruct u;reflexivity.
Qed.
Lemma literal_schnorr_signature_unpack_value (r s:Ty.tySem (Word 8)):
 @literal_schnorr_signature_unpack Alg.CoreFunSem (r,s)=
 if andb (@toZ (WordToZ 8) r <? canonical_field_order)
          (@toZ (WordToZ 8) s <? canonical_group_order) then inr (r,s) else inl tt.
Proof.
 pose proof (lt_word_spec_numeric 8 r canonical_field_word) as RCompare.
 pose proof (lt_word_spec_numeric 8 s canonical_group_word) as SCompare.
 rewrite canonical_field_word_value in RCompare.
 rewrite canonical_group_word_value in SCompare.
 rewrite <-RCompare,<-SCompare.
 unfold literal_schnorr_signature_unpack.
 cbn -[lt_word_spec Alg.scribe canonical_field_word canonical_group_word].
 rewrite !Alg.scribe_correct.
 change ((match (match @lt_word_spec Alg.CoreFunSem 8 (r,canonical_field_word) with
    | inl _=>inl tt|inr _=>@lt_word_spec Alg.CoreFunSem 8 (s,canonical_group_word) end) with
   | inl _=>inl tt|inr _=>inr (r,s) end :Ty.tySem (Ty.Sum Ty.Unit literal_schnorr_signature))=
   if andb (Bit.toBool (@lt_word_spec Alg.CoreFunSem 8 (r,canonical_field_word)))
           (Bit.toBool (@lt_word_spec Alg.CoreFunSem 8 (s,canonical_group_word)))
   then inr (r,s) else inl tt).
 destruct (@lt_word_spec Alg.CoreFunSem 8 (r,canonical_field_word)) as [u|u];destruct u;
 destruct (@lt_word_spec Alg.CoreFunSem 8 (s,canonical_group_word)) as [v|v];destruct v;reflexivity.
Qed.
Local Opaque literal_schnorr_pubkey_unpack_neg literal_schnorr_signature_unpack.
Lemma literal_bip0340_check_guarded_value (pk msg r s:Ty.tySem (Word 8)):
 @literal_bip0340_check Alg.CoreFunSem ((pk,msg),(r,s))=
 if @toZ (WordToZ 8) pk <? canonical_field_order then
   if andb (@toZ (WordToZ 8) r <? canonical_field_order)
           (@toZ (WordToZ 8) s <? canonical_group_order) then
    @literal_point_check Alg.CoreFunSem
      (((@canonical_scalar_normalize Alg.CoreFunSem (schnorr_challenge_hash_word r pk msg),
        (inr tt,pk)),s),(inl tt,r))
   else inl tt
 else inl tt.
Proof.
 rewrite literal_bip0340_check_value,literal_schnorr_pubkey_unpack_neg_value.
 destruct (@toZ (WordToZ 8) pk <? canonical_field_order);[|reflexivity].
 rewrite literal_schnorr_signature_unpack_value.
 destruct (andb (@toZ (WordToZ 8) r <? canonical_field_order)
                (@toZ (WordToZ 8) s <? canonical_group_order));[|reflexivity].
 cbn [fst snd];rewrite literal_bip0340_challenge_value;reflexivity.
Qed.

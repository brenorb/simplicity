(** Literal frozen Programs.CheckSig.sigHash and checkSigVerify composition. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Util.Option
 C.jet_secp_checksig_hash C.jet_secp_checksig_tag C.jet_secp_schnorr_verify_literal
 C.jet_secp_schnorr_challenge_literal.
Local Open Scope term_scope.
Set Default Timeout 10.
Module CS:=Alg.Core.Combinators.
Definition literal_checksig_args:=Ty.Prod (Ty.Prod (Word 8) (Word 9)) (Word 9).
Definition literal_checksig_hash {term:Alg.Core.Algebra}:term (Word 9) (Word 8):=
 (((Alg.scribe checksig_iv_word &&& iden) >>> @Simplicity.SHA256.hashBlock term)
  &&& Alg.scribe checksig_pad_word) >>> @Simplicity.SHA256.hashBlock term.
Lemma literal_checksig_hash_parametric:Alg.Core.Parametric (@literal_checksig_hash).
Proof.
 intros a b R;unfold literal_checksig_hash.
 repeat first [apply Simplicity.SHA256.hashBlock_Parametric|apply Alg.scribe_Parametric|
  apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.iden_Parametric].
Qed.
Local Opaque Simplicity.SHA256.hashBlock checksig_iv_word checksig_pad_word.
Lemma literal_checksig_hash_value (ir h:Ty.tySem (Word 8)):
 @literal_checksig_hash Alg.CoreFunSem (ir,h)=checksig_hash_word ir h.
Proof.
 unfold literal_checksig_hash,checksig_hash_word.
 cbn -[Simplicity.SHA256.hashBlock Alg.scribe checksig_iv_word checksig_pad_word].
 rewrite !Alg.scribe_correct;reflexivity.
Qed.
Definition literal_checksig_verify {term:Alg.Assertion.Algebra}:term literal_checksig_args Ty.Unit:=
 CS.comp
  (CS.pair (CS.take (CS.pair (CS.take CS.iden) (CS.drop (@literal_checksig_hash (Alg.Assertion.toCore term)))))
           (CS.drop CS.iden))
  (@literal_bip0340_verify term).
Lemma literal_checksig_verify_parametric:Alg.Assertion.Parametric (@literal_checksig_verify).
Proof.
 intros a b [R [HC HA]];unfold literal_checksig_verify.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - repeat first [apply (literal_checksig_hash_parametric _ _ (Alg.Core.Parametric.Pack HC))|
   apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC))|
   apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC))|
   apply (Alg.drop_Parametric (Alg.Core.Parametric.Pack HC))|
   apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC))].
 - apply (literal_bip0340_verify_parametric _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
Qed.
Local Opaque literal_checksig_hash literal_bip0340_verify.
Lemma literal_checksig_verify_option (pk ir h r s:Ty.tySem (Word 8)):
 @literal_checksig_verify (Alg.AssertionSem option_Monad_Zero) ((pk,(ir,h)),(r,s))=
 @literal_bip0340_verify (Alg.AssertionSem option_Monad_Zero) ((pk,checksig_hash_word ir h),(r,s)).
Proof.
 pose proof (Alg.CoreSem_initial (M:=option_CIMonad) literal_checksig_hash_parametric (ir,h)) as Core.
 change (@literal_checksig_hash (Alg.AssertionSem option_Monad_Zero) (ir,h)=
  Some (@literal_checksig_hash Alg.CoreFunSem (ir,h))) in Core.
 unfold literal_checksig_verify,CS.comp,CS.pair,CS.take,CS.drop,CS.iden.
 cbn [Alg.Core.comp Alg.Core.pair Alg.Core.take Alg.Core.drop Alg.Core.iden
   Alg.Core.class_of Alg.Assertion.toCore Alg.Assertion.base Alg.Assertion.class_of
   Alg.Assertion.packager Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
   Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
   Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
   option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 cbn [fst snd Monad.CIMonad.Theory.phi Monad.CIMonad.Theory.eta].
 lazymatch goal with |- context[@literal_checksig_hash ?alg (ir,h)]=>
  assert (Lift:@literal_checksig_hash alg (ir,h)=Some (@literal_checksig_hash Alg.CoreFunSem (ir,h))) by exact Core;
  rewrite Lift end.
 cbn [Monad.CIMonad.bind option_bind].
 rewrite literal_checksig_hash_value;reflexivity.
Qed.

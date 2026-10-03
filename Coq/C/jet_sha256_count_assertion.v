(** Literal mkLibAssert.verifyNumCompression from Programs/Sha256.hs:
    assert (ioh &&& (unit >>> scribe (toWord64 (2^55))) >>> lt word64).
    A guard bridge for the actual context reader, not public jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Import C.jet_order_spec C.jet_assertion_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read_sha256_overflow.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_count_limit : Ty.tySem (Word 6) := @fromZ (WordToZ 6) 36028797018963968.
Definition sha256_count_check_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term sha256_ctx8_type Bit :=
  AC.comp (AC.pair (AC.drop (AC.take AC.iden))
    (AC.comp AC.unit (Alg.scribe sha256_count_limit))) (@lt_word_spec term 6).
Definition sha256_count_assertion_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term sha256_ctx8_type Ty.Unit :=
  AC.comp (AC.pair (@sha256_count_check_spec term) AC.unit)
    (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (AC.take AC.iden)).

Lemma sha256_count_check_parametric : Alg.Core.Parametric (@sha256_count_check_spec).
Proof.
  intros alg1 alg2 R. unfold sha256_count_check_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.drop_Parametric, Alg.take_Parametric, Alg.iden_Parametric.
    + apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Alg.scribe_Parametric].
  - apply lt_word_spec_parametric.
Qed.

Lemma sha256_count_assertion_parametric : Alg.Assertion.Parametric (@sha256_count_assertion_spec).
Proof.
  intros alg1 alg2 [R [HC HA]]. unfold sha256_count_assertion_spec.
  apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
  - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC));
      [apply sha256_count_check_parametric|apply Alg.unit_Parametric].
  - apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
    apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC)); apply Alg.iden_Parametric.
Qed.

Lemma sha256_count_limit_numeric : @toZ (WordToZ 6) sha256_count_limit = 36028797018963968.
Proof. vm_compute; reflexivity. Qed.

Lemma sha256_count_check_numeric buf count state :
  Bit.toBool (@sha256_count_check_spec Alg.CoreFunSem (buf,(count,state))) =
    (@toZ (WordToZ 6) count <? 36028797018963968).
Proof.
  change (Bit.toBool (@lt_word_spec Alg.CoreFunSem 6
    (count, @Alg.scribe Ty.Unit (Word 6) sha256_count_limit Alg.CoreFunSem tt)) =
      (@toZ (WordToZ 6) count <? 36028797018963968)).
  rewrite Alg.scribe_correct, lt_word_spec_numeric, sha256_count_limit_numeric; reflexivity.
Qed.

Lemma sha256_count_assertion_option buf count state :
  @sha256_count_assertion_spec (Alg.AssertionSem option_Monad_Zero) (buf,(count,state)) =
    if @toZ (WordToZ 6) count <? 36028797018963968 then Some tt else None.
Proof.
  pose proof (Alg.CoreSem_initial (M := option_CIMonad)
    sha256_count_check_parametric (buf,(count,state))) as HCore.
  change (@sha256_count_check_spec (Alg.AssertionSem option_Monad_Zero) (buf,(count,state)) =
    Some (@sha256_count_check_spec Alg.CoreFunSem (buf,(count,state)))) in HCore.
  unfold sha256_count_assertion_spec, AC.comp, AC.pair.
  cbn [Alg.Core.comp Alg.Core.pair Alg.Core.class_of Alg.Assertion.toCore
    Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
    Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
    Monad.CIMonad.Theory.kleisliComp].
  unfold Monad.CIMonad.Theory.kleisliComp.
  cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
    Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
    option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
  match goal with |- context[@sha256_count_check_spec ?alg (buf,(count,state))] =>
    replace (@sha256_count_check_spec alg (buf,(count,state))) with
      (Some (@sha256_count_check_spec Alg.CoreFunSem (buf,(count,state)))) by (symmetry; exact HCore)
  end.
  change (match @sha256_count_check_spec Alg.CoreFunSem (buf,(count,state)) with
    | inl _ => None | inr x => Some x end =
      if @toZ (WordToZ 6) count <? 36028797018963968 then Some tt else None).
  rewrite <- (sha256_count_check_numeric buf count state).
  destruct (@sha256_count_check_spec Alg.CoreFunSem (buf,(count,state))) as [u|u]; destruct u; reflexivity.
Qed.

Lemma sha256_read_return_matches_count_assertion buf count state r :
  Int64.unsigned r = @toZ (WordToZ 6) count ->
  @sha256_count_assertion_spec (Alg.AssertionSem option_Monad_Zero) (buf,(count,state)) =
    if negb (sha256_read_overflow r) then Some tt else None.
Proof.
  intro Hr. rewrite sha256_count_assertion_option, <- Hr.
  destruct (sha256_read_overflow r) eqn:HO; cbn [negb].
  - apply sha256_read_overflow_true in HO.
    assert (HT : (Int64.unsigned r <? 36028797018963968) = Datatypes.false) by (apply Z.ltb_ge; exact HO).
    rewrite HT; reflexivity.
  - apply sha256_read_overflow_false in HO.
    assert (HT : (Int64.unsigned r <? 36028797018963968) = Datatypes.true) by (apply Z.ltb_lt; exact HO).
    rewrite HT; reflexivity.
Qed.

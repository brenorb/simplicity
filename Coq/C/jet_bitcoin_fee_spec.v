(** Canonical Transaction.fee program:
    [totalInputValue &&& totalOutputValue >>> subtract word64 >>> ih],
    and its value.  No C execution is claimed here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.List Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq C.jet_word_repr C.jet_predicate_spec C.jet_toZ.
Require Import C.jet_subtract_spec C.jet_bitcoin_totals_spec C.jet_bitcoin_totals_canonical.
Import ListNotations.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.
Set Default Timeout 60.

Definition fee_tail {alg : Core.Algebra} : alg (Word 6 * Word 6) (Word 6) :=
  @subtract_word_spec alg 6 >>> I H.

Definition fee_program {alg : Core.Algebra} (tin tout : alg Unit (Word 6)) : alg Unit (Word 6) :=
  (tin &&& tout) >>> fee_tail.

Lemma fee_tail_core_parametric : Core.Parametric (fun term => @fee_tail term).
Proof.
  intros alg1 alg2 R. unfold fee_tail.
  apply comp_Parametric; [apply subtract_word_spec_parametric|auto with parametricity].
Qed.

Lemma fee_program_parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
    (a1 b1 : alg1 Unit (Word 6)) (a2 b2 : alg2 Unit (Word 6)) :
  R _ _ a1 a2 -> R _ _ b1 b2 -> R _ _ (fee_program a1 b1) (fee_program a2 b2).
Proof.
  intros HA HB. unfold fee_program.
  apply comp_Parametric; [apply pair_Parametric; assumption|apply fee_tail_core_parametric].
Qed.

Lemma fee_tail_reader_sem {E : Type} (x : tySem (Word 6 * Word 6)) (environment : E) :
  @fee_tail (CoreSem (ReaderT_CIMonad E option_CIMonad)) x environment = Some (|[fee_tail]| x).
Proof.
  pose proof (@CoreSem_initial (ReaderT_CIMonad E option_CIMonad) _ _
    (fun term => @fee_tail term) fee_tail_core_parametric x) as Hs.
  refine (eq_trans (f_equal (fun f => f environment) Hs) _). reflexivity.
Qed.

Lemma fee_program_reader_sem {E : Type}
    (tin tout : CoreSem (ReaderT_CIMonad E option_CIMonad) Unit (Word 6)) (environment : E) x y :
  tin tt environment = Some x -> tout tt environment = Some y ->
  fee_program tin tout tt environment = Some (|[fee_tail]| (x, y)).
Proof.
  intros HX HY. unfold fee_program.
  assert (Htail : ltac:(let t := eval lazy beta iota zeta delta -[fee_tail] in
      (@fee_tail (CoreSem (ReaderT_CIMonad E option_CIMonad)) (x, y) environment) in
      exact (t = Some (|[fee_tail]| (x, y))))) by exact (fee_tail_reader_sem (x, y) environment).
  lazy beta iota zeta delta -[fee_tail] in HX, HY |- *.
  rewrite HX, HY. exact Htail.
Qed.

Local Open Scope Z_scope.

Lemma subtract_balance (a b : Word64) (c : Bit) (w : Word64) :
  @subtract_word_spec CoreFunSem 6 (a, b) = (c, w) ->
  wz 6 w - wsize 6 * toZ c = wz 6 a - wz 6 b.
Proof.
  intro Hr.
  pose proof (subtract_word_spec_numeric 6 a b) as Hc. rewrite Hr in Hc.
  unfold borrow_word_balance, word_modulus in Hc.
  rewrite two_power_nat_equiv, word_bitSize in Hc.
  exact Hc.
Qed.

Lemma fee_tail_fromZ x y : |[fee_tail]| (fw6 x, fw6 y) = fw6 (x - y).
Proof.
  assert (Hs : |[fee_tail]| (fw6 x, fw6 y) =
    snd (@subtract_word_spec CoreFunSem 6 (fw6 x, fw6 y))) by reflexivity.
  rewrite Hs. clear Hs.
  destruct (@subtract_word_spec CoreFunSem 6 (fw6 x, fw6 y)) as [c w] eqn:Hr.
  pose proof (subtract_balance _ _ _ _ Hr) as Hc.
  pose proof (wz_range 6 w) as Hw. pose proof (wsize_pos 6) as Hpos.
  rewrite (fw6_toZ x), (fw6_toZ y) in Hc.
  assert (Hsum : (x - y) mod wsize 6 = wz 6 w).
  { rewrite Zminus_mod.
    replace (x mod wsize 6 - y mod wsize 6) with (wz 6 w + (- toZ c) * wsize 6) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. exact Hw. }
  cbn [snd]. unfold fw6. rewrite <- (word_fromZ_mod 6 (x - y)).
  change (2 ^ Z.of_nat (Nat.pow 2 6)) with (wsize 6). rewrite Hsum.
  unfold wz. symmetry. apply from_toZ.
Qed.

Definition bitcoin_fee_spec {alg : Primitive.Algebra} : alg Ty.Unit Word64 :=
  fee_program bitcoin_total_input_value_spec bitcoin_total_output_value_spec.

Lemma bitcoin_fee_spec_parametric : Primitive.Parametric (@bitcoin_fee_spec).
Proof.
  intros alg1 alg2 [R [HA HP]]. unfold bitcoin_fee_spec.
  apply (fee_program_parametric (Alg.Core.Parametric.Pack (Alg.Assertion.Parametric.base HA))).
  - apply (bitcoin_total_input_value_spec_parametric _ _
      (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
  - apply (bitcoin_total_output_value_spec_parametric _ _
      (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma bitcoin_fee_spec_value (environment : Bitcoin.env) :
  @bitcoin_fee_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (fw6 (sigTxTotalInValue (Bitcoin.envTx environment) -
               sigTxTotalOutValue (Bitcoin.envTx environment))).
Proof.
  unfold bitcoin_fee_spec.
  rewrite <- fee_tail_fromZ.
  exact (@fee_program_reader_sem Bitcoin.env
    (@bitcoin_total_input_value_spec (PrimitivePrimSem option_Monad_Zero))
    (@bitcoin_total_output_value_spec (PrimitivePrimSem option_Monad_Zero)) environment _ _
    (bitcoin_total_input_value_spec_sum environment)
    (bitcoin_total_output_value_spec_sum environment)).
Qed.

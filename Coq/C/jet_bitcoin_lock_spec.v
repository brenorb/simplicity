(** Literal TimeLock.txLockHeight / txLockTime:
      [txIsFinal &&& primitive LockTime >>> cond z (parseLock >>> copair iden z)]
      [txIsFinal &&& primitive LockTime >>> cond z (parseLock >>> copair z iden)]
    with [z = unit >>> zero word32], and their values.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_forWhile_seq C.jet_word_repr C.jet_timelock_spec C.jet_bitcoin_is_final_spec.
Import ListNotations.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.
Set Default Timeout 60.

Definition lock_zero {A : Ty} {alg : Core.Algebra} : alg A Word32 := unit >>> zero (n := 5).

Definition lock_tail (height : bool) {alg : Core.Algebra} : alg (Bit * Word32) Word32 :=
  Bit.cond lock_zero
    (@parse_lock_spec alg >>>
      (if height then copair iden lock_zero else copair lock_zero iden)).

Definition lock_program (height : bool) {alg : Core.Algebra}
    (isfinal : alg Unit Bit) (locktime : alg Unit Word32) : alg Unit Word32 :=
  (isfinal &&& locktime) >>> lock_tail height.

Lemma lock_zero_parametric {A : Ty} {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2) :
  R A _ lock_zero lock_zero.
Proof. unfold lock_zero. auto with parametricity. Qed.

Lemma lock_tail_core_parametric height : Core.Parametric (fun term => @lock_tail height term).
Proof.
  intros alg1 alg2 R. unfold lock_tail.
  apply Bit.cond_Parametric; [apply lock_zero_parametric|].
  apply comp_Parametric; [apply parse_lock_spec_parametric|].
  destruct height; apply copair_Parametric;
    first [apply lock_zero_parametric|apply iden_Parametric].
Qed.

Lemma lock_program_parametric height {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
    (a1 : alg1 Unit Bit) (b1 : alg1 Unit Word32) (a2 : alg2 Unit Bit) (b2 : alg2 Unit Word32) :
  R _ _ a1 a2 -> R _ _ b1 b2 -> R _ _ (lock_program height a1 b1) (lock_program height a2 b2).
Proof.
  intros HA HB. unfold lock_program.
  apply comp_Parametric; [apply pair_Parametric; assumption|apply lock_tail_core_parametric].
Qed.

Lemma lock_tail_reader_sem height {E : Type} (x : tySem (Bit * Word32)) (environment : E) :
  @lock_tail height (CoreSem (ReaderT_CIMonad E option_CIMonad)) x environment =
    Some (|[lock_tail height]| x).
Proof.
  pose proof (@CoreSem_initial (ReaderT_CIMonad E option_CIMonad) _ _
    (fun term => @lock_tail height term) (lock_tail_core_parametric height) x) as Hs.
  refine (eq_trans (f_equal (fun f => f environment) Hs) _). reflexivity.
Qed.

Lemma lock_program_reader_sem height {E : Type}
    (isfinal : CoreSem (ReaderT_CIMonad E option_CIMonad) Unit Bit)
    (locktime : CoreSem (ReaderT_CIMonad E option_CIMonad) Unit Word32) (environment : E) x y :
  isfinal tt environment = Some x -> locktime tt environment = Some y ->
  lock_program height isfinal locktime tt environment = Some (|[lock_tail height]| (x, y)).
Proof.
  intros HX HY. unfold lock_program.
  assert (Htail : ltac:(let t := eval lazy beta iota zeta delta -[lock_tail] in
      (@lock_tail height (CoreSem (ReaderT_CIMonad E option_CIMonad)) (x, y) environment) in
      exact (t = Some (|[lock_tail height]| (x, y))))) by exact (lock_tail_reader_sem height (x, y) environment).
  lazy beta iota zeta delta -[lock_tail] in HX, HY |- *.
  rewrite HX, HY. exact Htail.
Qed.

Local Open Scope Z_scope.

Definition lock_value (height final : bool) (z : Z) : Z :=
  if final then 0
  else if z <? 500000000 then (if height then z else 0) else (if height then 0 else z).

Lemma zero_fw5 : |[zero (n := 5)]| tt = @fromZ (WordToZ 5) 0.
Proof.
  rewrite <- (from_toZ (|[zero (n := 5)]| tt)) at 1.
  rewrite (zero_correct 5). reflexivity.
Qed.

Lemma lock_tail_value height (final : bool) (w : tySem Word32) :
  |[lock_tail height]| (Bit.fromBool final, w) =
    @fromZ (WordToZ 5) (lock_value height final (@toZ (WordToZ 5) w)).
Proof.
  assert (Hs : |[lock_tail height]| (Bit.fromBool final, w) =
    if final then |[zero (n := 5)]| tt
    else match @parse_lock_spec CoreFunSem w with
         | inl h => if height then h else |[zero (n := 5)]| tt
         | inr t => if height then |[zero (n := 5)]| tt else t
         end).
  { unfold lock_tail. destruct final; [reflexivity|].
    cbn -[parse_lock_spec zero].
    destruct (@parse_lock_spec CoreFunSem w) as [h | t]; destruct height; reflexivity. }
  rewrite Hs. unfold lock_value. destruct final; [exact zero_fw5|].
  rewrite parse_lock_spec_numeric.
  destruct (@toZ (WordToZ 5) w <? 500000000); destruct height;
    first [exact zero_fw5|symmetry; apply from_toZ].
Qed.

Definition bitcoin_lock_time_prim {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  Primitive.Combinators.prim Bitcoin.LockTime.

Definition bitcoin_tx_lock_height_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  lock_program Datatypes.true bitcoin_tx_is_final_spec bitcoin_lock_time_prim.
Definition bitcoin_tx_lock_time_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  lock_program Datatypes.false bitcoin_tx_is_final_spec bitcoin_lock_time_prim.

Lemma bitcoin_lock_program_parametric height :
  Primitive.Parametric (fun alg => lock_program height (@bitcoin_tx_is_final_spec alg)
    (@bitcoin_lock_time_prim alg)).
Proof.
  intros alg1 alg2 [R [HA HP]].
  apply (lock_program_parametric height (Alg.Core.Parametric.Pack (Alg.Assertion.Parametric.base HA))).
  - apply (bitcoin_tx_is_final_spec_parametric _ _
      (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
  - apply (prim_Parametric (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma bitcoin_tx_lock_height_spec_parametric : Primitive.Parametric (@bitcoin_tx_lock_height_spec).
Proof. exact (bitcoin_lock_program_parametric Datatypes.true). Qed.
Lemma bitcoin_tx_lock_time_spec_parametric : Primitive.Parametric (@bitcoin_tx_lock_time_spec).
Proof. exact (bitcoin_lock_program_parametric Datatypes.false). Qed.

Definition bitcoin_lock_value height (environment : Bitcoin.env) : Z :=
  lock_value height (forallb sequence_final (sigTxIn (Bitcoin.envTx environment)))
    (Int.unsigned (sigTxLock (Bitcoin.envTx environment))).

Lemma bitcoin_lock_program_value height (environment : Bitcoin.env) :
  lock_program height (@bitcoin_tx_is_final_spec (PrimitivePrimSem option_Monad_Zero))
    (@bitcoin_lock_time_prim (PrimitivePrimSem option_Monad_Zero)) tt environment =
    Some (@fromZ (WordToZ 5) (bitcoin_lock_value height environment)).
Proof.
  unfold bitcoin_lock_value.
  assert (HL : @toZ (WordToZ 5) (@fromZ (WordToZ 5) (Int.unsigned (sigTxLock (Bitcoin.envTx environment)))) =
    Int.unsigned (sigTxLock (Bitcoin.envTx environment))).
  { rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
    apply Z.mod_small. exact (Int.unsigned_range _). }
  rewrite <- HL at 1. rewrite <- lock_tail_value.
  exact (@lock_program_reader_sem height Bitcoin.env
    (@bitcoin_tx_is_final_spec (PrimitivePrimSem option_Monad_Zero))
    (@bitcoin_lock_time_prim (PrimitivePrimSem option_Monad_Zero)) environment _ _
    (bitcoin_tx_is_final_spec_value environment) eq_refl).
Qed.

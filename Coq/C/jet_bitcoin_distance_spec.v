(** Literal TimeLock.txLockDistance / txLockDuration:
      [bip68VersionCheck &&& (currentSequence >>> parseSequence)
         >>> cond (copair (unit >>> z) (copair iden (unit >>> z))) (unit >>> z)]
    (resp. [copair (unit >>> z) iden]) with [z = zero word16] and
      [bip68VersionCheck = scribe (toWord32 2) &&& primitive Version >>> le word32],
    and their values.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_word_repr C.jet_order_spec C.jet_parse_sequence_spec C.jet_bitcoin_current_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.
Module DC := Alg.Core.Combinators.

Definition word16_zero {A : Ty} {alg : Core.Algebra} : alg A (Word 4) :=
  DC.comp DC.unit (@Word.zero 4 alg).

Definition dist_tail (dist : bool) {alg : Core.Algebra} :
    alg (Ty.Prod Bit (Ty.Sum Ty.Unit (Ty.Sum (Word 4) (Word 4)))) (Word 4) :=
  Bit.cond
    (DC.copair word16_zero
      (if dist then DC.copair DC.iden word16_zero else DC.copair word16_zero DC.iden))
    word16_zero.

Definition bip68_two : Ty.tySem (Word 5) := @fromZ (WordToZ 5) 2.

Definition bip68_core {alg : Core.Algebra} (version : alg Ty.Unit (Word 5)) : alg Ty.Unit Bit :=
  DC.comp (DC.pair (@Alg.scribe Ty.Unit (Word 5) bip68_two alg) version) (@le_word_spec alg 5).

Lemma word16_zero_parametric {A : Ty} {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2) :
  R A _ word16_zero word16_zero.
Proof. unfold word16_zero. auto with parametricity. Qed.

Lemma dist_tail_parametric dist : Core.Parametric (fun term => @dist_tail dist term).
Proof.
  intros alg1 alg2 R. unfold dist_tail.
  apply Bit.cond_Parametric; [|apply word16_zero_parametric].
  apply Alg.copair_Parametric; [apply word16_zero_parametric|].
  destruct dist; apply Alg.copair_Parametric;
    first [apply word16_zero_parametric|apply Alg.iden_Parametric].
Qed.

(** A closed core term runs in the reader monad as its functional semantics. *)
Lemma core_reader_sem {A B : Ty} (t : forall alg : Core.Algebra, alg A B)
    (Ht : Core.Parametric (fun alg => t alg)) {E : Type} (x : Ty.tySem A) (environment : E) :
  t (CoreSem (ReaderT_CIMonad E option_CIMonad)) x environment = Some (t CoreFunSem x).
Proof.
  pose proof (@CoreSem_initial (ReaderT_CIMonad E option_CIMonad) _ _ (fun alg => t alg) Ht x) as Hs.
  refine (eq_trans (f_equal (fun f => f environment) Hs) _). reflexivity.
Qed.

Definition bitcoin_pair {alg : Primitive.Algebra} {A B C} (p : alg A B) (q : alg A C) :
    alg A (Ty.Prod B C) := DC.pair p q.

Lemma bitcoin_pair_sem {A B C} (p : Ty.tySem A -> Bitcoin.env -> option (Ty.tySem B))
    (q : Ty.tySem A -> Bitcoin.env -> option (Ty.tySem C)) (a : Ty.tySem A) env :
  @bitcoin_pair (PrimitivePrimSem option_Monad_Zero) A B C p q a env =
    match p a env, q a env with Some b, Some c => Some (b, c) | _, _ => None end.
Proof.
  unfold bitcoin_pair.
  remember (p a env) as r eqn:HR. remember (q a env) as s eqn:HS.
  destruct r as [b | ]; destruct s as [c | ];
    lazy beta iota zeta delta in HR, HS |- *;
    rewrite <- ?HR, <- ?HS; reflexivity.
Qed.

Definition bitcoin_core {A B} (t : forall alg : Core.Algebra, alg A B) {alg : Primitive.Algebra} :
    alg A B := t _.

Lemma bitcoin_core_sem {A B} (t : forall alg : Core.Algebra, alg A B)
    (Ht : Core.Parametric (fun alg => t alg)) (a : Ty.tySem A) (env : Bitcoin.env) :
  @bitcoin_core A B t (PrimitivePrimSem option_Monad_Zero) a env = Some (t CoreFunSem a).
Proof. exact (@core_reader_sem A B t Ht Bitcoin.env a env). Qed.

Definition bitcoin_version_prim {alg : Primitive.Algebra} : alg Ty.Unit (Word 5) :=
  Primitive.Combinators.prim Bitcoin.Version.

Definition bitcoin_bip68_spec {alg : Primitive.Algebra} : alg Ty.Unit Bit :=
  bitcoin_comp
    (bitcoin_pair (bitcoin_core (fun alg => @Alg.scribe Ty.Unit (Word 5) bip68_two alg))
      bitcoin_version_prim)
    (bitcoin_core (fun alg => @le_word_spec alg 5)).

Definition bitcoin_lock_distance_program (dist : bool) {alg : Primitive.Algebra} : alg Ty.Unit (Word 4) :=
  bitcoin_comp
    (bitcoin_pair bitcoin_bip68_spec
      (bitcoin_comp bitcoin_current_sequence_spec (bitcoin_core (@parse_sequence_spec))))
    (bitcoin_core (fun alg => @dist_tail dist alg)).

Definition bitcoin_tx_lock_distance_spec {alg : Primitive.Algebra} : alg Ty.Unit (Word 4) :=
  bitcoin_lock_distance_program Datatypes.true.
Definition bitcoin_tx_lock_duration_spec {alg : Primitive.Algebra} : alg Ty.Unit (Word 4) :=
  bitcoin_lock_distance_program Datatypes.false.

Definition dist_value (dist ok : bool) (s : Z) : Z :=
  if andb (andb ok (negb (Z.testbit s 31))) (if dist then negb (Z.testbit s 22) else Z.testbit s 22)
  then s else 0.

Lemma zero_fw4 : @Word.zero 4 CoreFunSem tt = @fromZ (WordToZ 4) 0.
Proof.
  rewrite <- (from_toZ (@Word.zero 4 CoreFunSem tt)) at 1.
  rewrite (zero_correct 4). reflexivity.
Qed.

Lemma dist_tail_value dist (vb : Ty.tySem Bit) (s : Ty.tySem (Word 5)) :
  @dist_tail dist CoreFunSem (vb, @parse_sequence_spec CoreFunSem s) =
    @fromZ (WordToZ 4) (dist_value dist (Bit.toBool vb) (@toZ (WordToZ 5) s)).
Proof.
  assert (Hs : forall p, @dist_tail dist CoreFunSem (vb, p) =
    if Bit.toBool vb then
      match p with
      | inl _ => @Word.zero 4 CoreFunSem tt
      | inr (inl x) => if dist then x else @Word.zero 4 CoreFunSem tt
      | inr (inr x) => if dist then @Word.zero 4 CoreFunSem tt else x
      end
    else @Word.zero 4 CoreFunSem tt).
  { intro p. unfold dist_tail.
    destruct vb as [ [] | [] ]; destruct p as [ [] | [x | x] ]; destruct dist; reflexivity. }
  rewrite Hs, parse_sequence_spec_numeric. unfold dist_value.
  destruct (Bit.toBool vb); [|exact zero_fw4].
  destruct (Z.testbit (@toZ (WordToZ 5) s) 31); [exact zero_fw4|].
  destruct (Z.testbit (@toZ (WordToZ 5) s) 22); destruct dist; cbn [andb negb];
    first [exact zero_fw4|reflexivity].
Qed.

Lemma bitcoin_version_word (environment : Bitcoin.env) :
  @toZ (WordToZ 5) (@fromZ (WordToZ 5) (Int.signed (sigTxVersion (Bitcoin.envTx environment)))) =
    Int.unsigned (sigTxVersion (Bitcoin.envTx environment)).
Proof.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  rewrite <- (Int.repr_signed (sigTxVersion (Bitcoin.envTx environment))) at 2.
  rewrite Int.unsigned_repr_eq. reflexivity.
Qed.

Lemma bitcoin_bip68_spec_value (environment : Bitcoin.env) :
  exists vb, @bitcoin_bip68_spec (PrimitivePrimSem option_Monad_Zero) tt environment = Some vb /\
    Bit.toBool vb = (2 <=? Int.unsigned (sigTxVersion (Bitcoin.envTx environment))).
Proof.
  eexists. split.
  - unfold bitcoin_bip68_spec. rewrite bitcoin_comp_sem, bitcoin_pair_sem.
    rewrite (bitcoin_core_sem (fun alg => @Alg.scribe Ty.Unit (Word 5) bip68_two alg))
      by (intros alg1 alg2 R; apply Alg.scribe_Parametric).
    assert (HV : @bitcoin_version_prim (PrimitivePrimSem option_Monad_Zero) tt environment =
      Some (@fromZ (WordToZ 5) (Int.signed (sigTxVersion (Bitcoin.envTx environment))))) by reflexivity.
    rewrite HV.
    apply (bitcoin_core_sem (fun alg => @le_word_spec alg 5) (le_word_spec_parametric 5)).
  - rewrite le_word_spec_numeric, Alg.scribe_correct, bitcoin_version_word. reflexivity.
Qed.

Lemma bitcoin_lock_distance_program_value dist (environment : Bitcoin.env) :
  exists txi, nth_error (sigTxIn (Bitcoin.envTx environment)) (Bitcoin.envIx environment) = Some txi /\
    @bitcoin_lock_distance_program dist (PrimitivePrimSem option_Monad_Zero) tt environment =
      Some (@fromZ (WordToZ 4) (dist_value dist
        (2 <=? Int.unsigned (sigTxVersion (Bitcoin.envTx environment)))
        (Int.unsigned (sigTxiSequence txi)))).
Proof.
  destruct (bitcoin_current_sequence_sem environment) as (txi & Hnth & Hseq).
  destruct (bitcoin_bip68_spec_value environment) as (vb & Hbip & Hvb).
  exists txi. split; [exact Hnth|].
  unfold bitcoin_lock_distance_program.
  rewrite bitcoin_comp_sem, bitcoin_pair_sem, Hbip, bitcoin_comp_sem, Hseq.
  rewrite (bitcoin_core_sem (@parse_sequence_spec) parse_sequence_spec_parametric).
  rewrite (bitcoin_core_sem (fun alg => @dist_tail dist alg) (dist_tail_parametric dist)).
  rewrite dist_tail_value, Hvb.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  rewrite Z.mod_small by exact (Int.unsigned_range (sigTxiSequence txi)).
  reflexivity.
Qed.

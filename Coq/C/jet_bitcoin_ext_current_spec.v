(** Canonical specifications of the extended "current input" Bitcoin jets:
    [primitive CurrentIndex >>> assert (primitive InputX)] over the extended
    primitive signature, with the literal Programs.Bit.assert. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Digest Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin C.jet_assertion_spec C.jet_word_repr C.jet_bitcoin_current_spec.
Require Import C.jet_bitcoin_ext_prim.
Import ListNotations.
Local Open Scope Z_scope.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Set Default Timeout 60.

Definition ext_assert_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} {A B} (t : alg A (Ty.Sum Ty.Unit B)) : alg A B :=
  Alg.Core.Combinators.comp (Alg.Core.Combinators.pair t Alg.Core.Combinators.unit)
    (Alg.Assertion.Combinators.assertr assertion_cmr_fail0
      (Alg.Core.Combinators.take Alg.Core.Combinators.iden)).

Lemma ext_assert_sem {A B} (t : Ty.tySem A -> ext_environment -> option (Ty.tySem (Ty.Sum Ty.Unit B)))
    (a : Ty.tySem A) env :
  @ext_assert_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) A B t a env =
    match t a env with Some (inr b) => Some b | _ => None end.
Proof.
  unfold ext_assert_spec.
  remember (t a env) as r eqn:HR.
  destruct r as [[u | b] | ];
    lazy beta iota zeta delta -[assertion_cmr_fail0] in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition ext_comp {alg : PrimitiveBitcoinExt.Primitive.Algebra} {A B C} (p : alg A B) (q : alg B C) : alg A C :=
  Alg.Core.Combinators.comp p q.

Lemma ext_comp_sem {A B C} (p : Ty.tySem A -> ext_environment -> option (Ty.tySem B))
    (q : Ty.tySem B -> ext_environment -> option (Ty.tySem C)) (a : Ty.tySem A) env :
  @ext_comp (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) A B C p q a env =
    match p a env with Some b => q b env | None => None end.
Proof.
  unfold ext_comp.
  remember (p a env) as r eqn:HR.
  destruct r as [b | ];
    lazy beta iota zeta delta in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition ext_ix (e : ext_environment) : nat := Bitcoin.envIx (extBase e).

Definition bitcoin_current_script_hash_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} : alg Ty.Unit Word256 :=
  ext_comp (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.CurrentIndex)
    (ext_assert_spec (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InputScriptHash)).

Definition bitcoin_current_script_sig_hash_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} : alg Ty.Unit Word256 :=
  ext_comp (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.CurrentIndex)
    (ext_assert_spec (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InputScriptSigHash)).

Lemma ext_ix_lt (environment : ext_environment) (hs : list hash256) :
  length hs = length (sigTxIn (Bitcoin.envTx (extBase environment))) ->
  exists h, nth_error hs (ext_ix environment) = Some h.
Proof.
  intros Hl. pose proof (Bitcoin.envIxBounded (extBase environment)) as Hb.
  destruct (nth_error hs (ext_ix environment)) as [h|] eqn:Hn; [eauto|].
  apply nth_error_None in Hn. unfold ext_ix in Hn. lia.
Qed.

Lemma bitcoin_current_script_hash_sem (environment : ext_environment) :
  exists h, nth_error (extInScriptHash environment) (ext_ix environment) = Some h /\
    @bitcoin_current_script_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) tt environment = Some (from_hash256 h).
Proof.
  destruct (ext_ix_lt environment (extInScriptHash environment) (extInScriptHash_len environment))
    as (h & Hnth). exists h. split; [exact Hnth|].
  unfold bitcoin_current_script_hash_spec. rewrite ext_comp_sem.
  assert (HCI : @PrimitiveBitcoinExt.Primitive.Combinators.prim Ty.Unit Word32 (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    BitcoinExt.CurrentIndex tt environment =
    Some (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment)))) by reflexivity.
  rewrite HCI. rewrite ext_assert_sem.
  assert (HIV : @PrimitiveBitcoinExt.Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word256) (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    BitcoinExt.InputScriptHash (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment))) environment =
    BitcoinExt.sem BitcoinExt.InputScriptHash (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment))) environment)
    by reflexivity.
  rewrite HIV. unfold BitcoinExt.sem. cbv zeta.
  unfold ext_ix in *.
  rewrite (bitcoin_ix_word (extBase environment)), Nat2Z.id. rewrite Hnth. reflexivity.
Qed.

Lemma bitcoin_current_script_sig_hash_sem (environment : ext_environment) :
  exists h, nth_error (extInScriptSigHash environment) (ext_ix environment) = Some h /\
    @bitcoin_current_script_sig_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) tt environment = Some (from_hash256 h).
Proof.
  destruct (ext_ix_lt environment (extInScriptSigHash environment) (extInScriptSigHash_len environment))
    as (h & Hnth). exists h. split; [exact Hnth|].
  unfold bitcoin_current_script_sig_hash_spec. rewrite ext_comp_sem.
  assert (HCI : @PrimitiveBitcoinExt.Primitive.Combinators.prim Ty.Unit Word32 (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    BitcoinExt.CurrentIndex tt environment =
    Some (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment)))) by reflexivity.
  rewrite HCI. rewrite ext_assert_sem.
  assert (HIV : @PrimitiveBitcoinExt.Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word256) (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    BitcoinExt.InputScriptSigHash (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment))) environment =
    BitcoinExt.sem BitcoinExt.InputScriptSigHash (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment))) environment)
    by reflexivity.
  rewrite HIV. unfold BitcoinExt.sem. cbv zeta.
  unfold ext_ix in *.
  rewrite (bitcoin_ix_word (extBase environment)), Nat2Z.id. rewrite Hnth. reflexivity.
Qed.


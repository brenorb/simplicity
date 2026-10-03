(** Canonical specifications of the "current input" Bitcoin jets:
    [primitive CurrentIndex >>> assert (primitive InputX)], following
    Simplicity.Bitcoin.Programs.Transaction.  Here [assert] is the literal
    Programs.Bit.assert (a pair with unit and an assertr with the fail0 hash). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin C.jet_assertion_spec C.jet_word_repr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition bitcoin_assert_spec {alg : Primitive.Algebra} {A B} (t : alg A (Ty.Sum Ty.Unit B)) : alg A B :=
  Alg.Core.Combinators.comp (Alg.Core.Combinators.pair t Alg.Core.Combinators.unit)
    (Alg.Assertion.Combinators.assertr assertion_cmr_fail0
      (Alg.Core.Combinators.take Alg.Core.Combinators.iden)).

Lemma bitcoin_assert_sem {A B} (t : Ty.tySem A -> Bitcoin.env -> option (Ty.tySem (Ty.Sum Ty.Unit B)))
    (a : Ty.tySem A) env :
  @bitcoin_assert_spec (PrimitivePrimSem option_Monad_Zero) A B t a env =
    match t a env with Some (inr b) => Some b | _ => None end.
Proof.
  unfold bitcoin_assert_spec.
  remember (t a env) as r eqn:HR.
  destruct r as [[u | b] | ];
    lazy beta iota zeta delta -[assertion_cmr_fail0] in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition bitcoin_comp {alg : Primitive.Algebra} {A B C} (p : alg A B) (q : alg B C) : alg A C :=
  Alg.Core.Combinators.comp p q.

Lemma bitcoin_comp_sem {A B C} (p : Ty.tySem A -> Bitcoin.env -> option (Ty.tySem B))
    (q : Ty.tySem B -> Bitcoin.env -> option (Ty.tySem C)) (a : Ty.tySem A) env :
  @bitcoin_comp (PrimitivePrimSem option_Monad_Zero) A B C p q a env =
    match p a env with Some b => q b env | None => None end.
Proof.
  unfold bitcoin_comp.
  remember (p a env) as r eqn:HR.
  destruct r as [b | ];
    lazy beta iota zeta delta in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition bitcoin_current_value_spec {alg : Primitive.Algebra} : alg Ty.Unit Word64 :=
  bitcoin_comp (Primitive.Combinators.prim Bitcoin.CurrentIndex)
    (bitcoin_assert_spec (Primitive.Combinators.prim Bitcoin.InputValue)).

Definition bitcoin_current_sequence_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  bitcoin_comp (Primitive.Combinators.prim Bitcoin.CurrentIndex)
    (bitcoin_assert_spec (Primitive.Combinators.prim Bitcoin.InputSequence)).

Lemma bitcoin_ix_word (environment : Bitcoin.env) :
  toZ (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))) = Z.of_nat (Bitcoin.envIx environment).
Proof.
  pose proof (Bitcoin.envIxBounded environment) as Hb.
  pose proof (sigTxInBounds (Bitcoin.envTx environment)) as Hn.
  rewrite Zlength_correct in Hn.
  rewrite to_fromZ. change (two_power_nat (bitSize (WordToZ 5))) with 4294967296.
  apply Z.mod_small. split; [lia|]. change (0 < Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) < Int.modulus) in Hn.
  change Int.modulus with 4294967296 in Hn. lia.
Qed.

Lemma bitcoin_current_value_sem (environment : Bitcoin.env) :
  exists txi, nth_error (sigTxIn (Bitcoin.envTx environment)) (Bitcoin.envIx environment) = Some txi /\
    @bitcoin_current_value_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
      Some (@fromZ (WordToZ 6) (Int64.signed (sigTxiValue txi))).
Proof.
  pose proof (Bitcoin.envIxBounded environment) as Hb.
  destruct (nth_error (sigTxIn (Bitcoin.envTx environment)) (Bitcoin.envIx environment)) as [txi|] eqn:Hnth;
    [|apply nth_error_None in Hnth; lia].
  exists txi. split; [reflexivity|].
  unfold bitcoin_current_value_spec.
  rewrite bitcoin_comp_sem.
  assert (HCI : @Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero)
    Bitcoin.CurrentIndex tt environment = Some (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))))
    by reflexivity.
  rewrite HCI.
  rewrite bitcoin_assert_sem.
  assert (HIV : @Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word64) (PrimitivePrimSem option_Monad_Zero)
    Bitcoin.InputValue (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))) environment =
    Bitcoin.sem Bitcoin.InputValue (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))) environment)
    by reflexivity.
  rewrite HIV. unfold Bitcoin.sem. cbv zeta.
  rewrite bitcoin_ix_word, Nat2Z.id, Hnth. reflexivity.
Qed.

Lemma bitcoin_current_sequence_sem (environment : Bitcoin.env) :
  exists txi, nth_error (sigTxIn (Bitcoin.envTx environment)) (Bitcoin.envIx environment) = Some txi /\
    @bitcoin_current_sequence_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
      Some (@fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi))).
Proof.
  pose proof (Bitcoin.envIxBounded environment) as Hb.
  destruct (nth_error (sigTxIn (Bitcoin.envTx environment)) (Bitcoin.envIx environment)) as [txi|] eqn:Hnth;
    [|apply nth_error_None in Hnth; lia].
  exists txi. split; [reflexivity|].
  unfold bitcoin_current_sequence_spec.
  rewrite bitcoin_comp_sem.
  assert (HCI : @Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero)
    Bitcoin.CurrentIndex tt environment = Some (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))))
    by reflexivity.
  rewrite HCI.
  rewrite bitcoin_assert_sem.
  assert (HIV : @Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word32) (PrimitivePrimSem option_Monad_Zero)
    Bitcoin.InputSequence (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))) environment =
    Bitcoin.sem Bitcoin.InputSequence (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment))) environment)
    by reflexivity.
  rewrite HIV. unfold Bitcoin.sem. cbv zeta.
  rewrite bitcoin_ix_word, Nat2Z.id, Hnth. reflexivity.
Qed.

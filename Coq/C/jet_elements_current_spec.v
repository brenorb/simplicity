(** Ported from [jet_bitcoin_current_spec] (assert/comp semantics); the
    per-primitive statements are replaced by one generic lemma.

    Canonical specifications of the "current input" Elements jets:
    [primitive CurrentIndex >>> assert (primitive InputX)], following
    Simplicity.Elements.Programs.Transaction.  Here [assert] is the literal
    Programs.Bit.assert (a pair with unit and an assertr with the fail0 hash). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jet_assertion_spec C.jet_word_repr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition elements_assert_spec {alg : Primitive.Algebra} {A B} (t : alg A (Ty.Sum Ty.Unit B)) : alg A B :=
  Alg.Core.Combinators.comp (Alg.Core.Combinators.pair t Alg.Core.Combinators.unit)
    (Alg.Assertion.Combinators.assertr assertion_cmr_fail0
      (Alg.Core.Combinators.take Alg.Core.Combinators.iden)).

Lemma elements_assert_sem {A B} (t : Ty.tySem A -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit B)))
    (a : Ty.tySem A) env :
  @elements_assert_spec (PrimitivePrimSem option_Monad_Zero) A B t a env =
    match t a env with Some (inr b) => Some b | _ => None end.
Proof.
  unfold elements_assert_spec.
  remember (t a env) as r eqn:HR.
  destruct r as [[u | b] | ];
    lazy beta iota zeta delta -[assertion_cmr_fail0] in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition elements_comp {alg : Primitive.Algebra} {A B C} (p : alg A B) (q : alg B C) : alg A C :=
  Alg.Core.Combinators.comp p q.

Lemma elements_comp_sem {A B C} (p : Ty.tySem A -> Elements.env -> option (Ty.tySem B))
    (q : Ty.tySem B -> Elements.env -> option (Ty.tySem C)) (a : Ty.tySem A) env :
  @elements_comp (PrimitivePrimSem option_Monad_Zero) A B C p q a env =
    match p a env with Some b => q b env | None => None end.
Proof.
  unfold elements_comp.
  remember (p a env) as r eqn:HR.
  destruct r as [b | ];
    lazy beta iota zeta delta in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition elements_current_spec {alg : Primitive.Algebra} {B}
    (p : alg Word32 (Ty.Sum Ty.Unit B)) : alg Ty.Unit B :=
  elements_comp (Primitive.Combinators.prim Elements.CurrentIndex) (elements_assert_spec p).

Lemma elements_ix_word (environment : Elements.env) :
  toZ (@fromZ (WordToZ 5) (Z.of_nat (Elements.envIx environment))) = Z.of_nat (Elements.envIx environment).
Proof.
  pose proof (Elements.envIxWord32 environment) as Hb.
  rewrite to_fromZ. change (two_power_nat (bitSize (WordToZ 5))) with 4294967296.
  apply Z.mod_small. lia.
Qed.

(** Any per-input primitive of the [atInput] form, at the current index. *)
Lemma elements_current_sem {B : Ty}
    (t : Ty.tySem Word32 -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit B)))
    (f : sigTxInput -> Ty.tySem B) :
  (forall a e, t a e = Some (match nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ a)) with
                             | Some txi => inr (f txi)
                             | None => inl tt
                             end)) ->
  forall environment : Elements.env,
  exists txi, nth_error (sigTxIn (Elements.envTx environment)) (Elements.envIx environment) = Some txi /\
    @elements_current_spec (PrimitivePrimSem option_Monad_Zero) B t tt environment = Some (f txi).
Proof.
  intros Ht environment.
  pose proof (Elements.envIxBounded environment) as Hb.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Elements.envIx environment)) as [txi|] eqn:Hnth;
    [|apply nth_error_None in Hnth; lia].
  exists txi. split; [reflexivity|].
  unfold elements_current_spec.
  rewrite elements_comp_sem.
  assert (HCI : @Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero)
    Elements.CurrentIndex tt environment = Some (@fromZ (WordToZ 5) (Z.of_nat (Elements.envIx environment))))
    by reflexivity.
  rewrite HCI.
  rewrite elements_assert_sem.
  rewrite Ht, elements_ix_word, Nat2Z.id, Hnth. reflexivity.
Qed.

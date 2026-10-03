(** Literal Programs.Word.forWhile recursion from the canonical Haskell library.
    This is search infrastructure, not a public C-jet equivalence theorem. *)
From Coq Require Import List.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Bit Simplicity.Word.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Implicit Arguments.
Set Default Timeout 10.

(** SingleV performs counters false then true, stopping on Left. DoubleV
    nests two smaller loops with the high counter outside the low counter.
    Routing and pair/case structure are kept identical to Programs.Word. *)
Fixpoint for_while_program (n : nat) {C B A : Ty} {alg : Core.Algebra}
    (body : alg ((C * Word n) * A) (B + A)) : alg (C * A) (B + A) :=
  match n as k return alg ((C * Word k) * A) (B + A) -> alg (C * A) (B + A) with
  | 0 => fun body =>
      ((((O H &&& Bit.false) &&& I H) >>> body) &&& O H) >>>
        case (injl (O H)) (((I H &&& Bit.true) &&& O H) >>> body)
  | S k => fun body =>
      for_while_program k (for_while_program k
        (((O O O H &&& (O O I H &&& O I H)) &&& I H) >>> body))
  end body.

Lemma for_while_program_parametric n {C B A : Ty}
    {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
    (body1 : alg1 ((C * Word n) * A) (B + A))
    (body2 : alg2 ((C * Word n) * A) (B + A)) :
  R _ _ body1 body2 -> R _ _ (for_while_program n body1) (for_while_program n body2).
Proof.
  revert C B A body1 body2. induction n; intros C B A body1 body2 HB.
  - cbn [for_while_program]. auto 12 with parametricity.
  - cbn [for_while_program]. apply IHn. apply IHn.
    auto 12 with parametricity.
Qed.

(** Structural operational interpretation: None propagates, Left stops, and
    Right supplies the next state. It does not enumerate the 2^32 counters. *)
Fixpoint for_while_run (n : nat) {C B A : Ty}
    (body : tySem ((C * Word n) * A) -> option (tySem (B + A)))
    (context : tySem C) (state : tySem A) : option (tySem (B + A)) :=
  match n as k return
      (tySem ((C * Word k) * A) -> option (tySem (B + A))) ->
      option (tySem (B + A)) with
  | 0 => fun body =>
      match body ((context, Bit.zero), state) with
      | None => None
      | Some (inl result) => Some (inl result)
      | Some (inr next) => body ((context, Bit.one), next)
      end
  | S k => fun body =>
      @for_while_run k C B A
        (fun p => @for_while_run k (C * Word k) B A
          (fun q => body ((fst (fst (fst q)), (snd (fst (fst q)), snd (fst q))), snd q))
          (fst p) (snd p)) context state
  end body.

Lemma for_while_run_ext n {C B A : Ty}
    (body1 body2 : tySem ((C * Word n) * A) -> option (tySem (B + A)))
    (context : tySem C) (state : tySem A) :
  (forall p, body1 p = body2 p) ->
  for_while_run n body1 context state = for_while_run n body2 context state.
Proof.
  revert C B A body1 body2 context state.
  induction n; intros C B A body1 body2 context state HB.
  - cbn [for_while_run]. rewrite HB.
    destruct (body2 ((context, Bit.zero), state)) as [[result | next_state] | ];
      auto.
  - cbn [for_while_run]. apply IHn. intros p.
    apply IHn. intros q. apply HB.
Qed.

Lemma for_while_program_reader_sem n {E : Type} {C B A : Ty}
    (body : CoreSem (ReaderT_CIMonad E option_CIMonad) ((C * Word n) * A) (B + A))
    (context : tySem C) (state : tySem A) (environment : E) :
  for_while_program n body (context, state) environment =
    for_while_run n (fun p => body p environment) context state.
Proof.
  revert C B A body context state. induction n; intros C B A body context state.
  - cbn [for_while_program for_while_run].
    destruct (body ((context, Bit.zero), state) environment) as [[result | next_state] | ] eqn:HB;
      lazy beta iota zeta delta in HB |- *; rewrite HB; reflexivity.
  - cbn [for_while_program for_while_run]. rewrite IHn.
    apply for_while_run_ext. intros [[c hi] s]. rewrite IHn.
    apply for_while_run_ext. intros [[[c' hi'] lo] s'].
    reflexivity.
Qed.

(** Literal TimeLock.txIsFinal: a [forWhile] loop over the Word32 counters
    testing [all word32] on InputSequence until the first out-of-range counter.
    Semantic reduction to [forallb] over the input list.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq C.jet_word_repr C.jet_predicate_spec.
Import ListNotations.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.
Set Default Timeout 60.

Definition final_tail {alg : Core.Algebra} : alg Word32 (Bit + Unit) :=
  @predicate_spec 5 Datatypes.true alg >>> copair (injl Bit.false) (injr unit).

Definition final_body {alg : Core.Algebra} (op : alg Word32 (Unit + Word32)) :
    alg ((Unit * Word 5) * Unit) (Bit + Unit) :=
  take (drop op) >>> copair (injl Bit.true) final_tail.

Definition final_program {alg : Core.Algebra} (op : alg Word32 (Unit + Word32)) : alg Unit Bit :=
  (unit &&& unit) >>> for_while_program 5 (final_body op) >>> copair iden Bit.true.

Lemma final_tail_core_parametric : Core.Parametric (fun term => @final_tail term).
Proof.
  intros alg1 alg2 R. unfold final_tail.
  apply comp_Parametric; [apply predicate_spec_parametric|].
  unfold Bit.false. auto 12 with parametricity.
Qed.

Lemma final_program_parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
    (op1 : alg1 Word32 (Unit + Word32)) (op2 : alg2 Word32 (Unit + Word32)) :
  R _ _ op1 op2 -> R _ _ (final_program op1) (final_program op2).
Proof.
  intro HO. unfold final_program.
  apply comp_Parametric; [auto with parametricity|].
  apply comp_Parametric; [|unfold Bit.true; auto 12 with parametricity].
  apply for_while_program_parametric. unfold final_body.
  apply comp_Parametric; [auto with parametricity|].
  apply copair_Parametric; [unfold Bit.true; auto 12 with parametricity|apply final_tail_core_parametric].
Qed.

Definition final_step (op : tySem Word32 -> option (tySem (Unit + Word32)))
    (p : tySem ((Unit * Word 5) * Unit)) : option (tySem (Bit + Unit)) :=
  match op (snd (fst p)) with
  | None => None
  | Some (inl _) => Some (inl Bit.one)
  | Some (inr v) => Some (|[final_tail]| v)
  end.

Lemma final_tail_reader_sem {E : Type} (x : tySem Word32) (environment : E) :
  @final_tail (CoreSem (ReaderT_CIMonad E option_CIMonad)) x environment = Some (|[final_tail]| x).
Proof.
  pose proof (@CoreSem_initial (ReaderT_CIMonad E option_CIMonad) _ _
    (fun term => @final_tail term) final_tail_core_parametric x) as Hs.
  refine (eq_trans (f_equal (fun f => f environment) Hs) _). reflexivity.
Qed.

Lemma final_body_reader_sem {E : Type} (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Unit + Word32))
    (p : tySem ((Unit * Word 5) * Unit)) (environment : E) :
  final_body op p environment = final_step (fun w => op w environment) p.
Proof.
  destruct p as [[[] w] []]. unfold final_body, final_step.
  destruct (op w environment) as [[a | b] | ] eqn:HO.
  - lazy beta iota zeta delta -[final_tail] in HO |- *. rewrite HO. reflexivity.
  - lazy beta iota zeta delta -[final_tail] in HO |- *. rewrite HO.
    assert (Htail : ltac:(let t := eval lazy beta iota zeta delta -[final_tail] in
      (@final_tail (CoreSem (ReaderT_CIMonad E option_CIMonad)) b environment) in
      exact (t = Some (|[final_tail]| b)))) by exact (final_tail_reader_sem b environment).
    rewrite Htail. reflexivity.
  - lazy beta iota zeta delta -[final_tail] in HO |- *. rewrite HO. reflexivity.
Qed.

Lemma final_program_reader_finish {E : Type}
    (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Unit + Word32)) (environment : E) :
  final_program op tt environment =
    option_bind (fun result : tySem (Bit + Unit) =>
        match result with inl x => Some x | inr _ => Some Bit.one end)
      (@for_while_program 5 Unit Bit Unit (CoreSem (ReaderT_CIMonad E option_CIMonad))
        (final_body op) (tt, tt) environment).
Proof.
  unfold final_program.
  remember (@for_while_program 5 Unit Bit Unit (CoreSem (ReaderT_CIMonad E option_CIMonad))
        (final_body op) (tt, tt) environment) as result eqn:HR.
  destruct result as [[x | []] | ].
  - lazy beta iota zeta delta -[for_while_program final_body] in HR |- *. rewrite <- HR. reflexivity.
  - lazy beta iota zeta delta -[for_while_program final_body] in HR |- *. rewrite <- HR. reflexivity.
  - lazy beta iota zeta delta -[for_while_program final_body] in HR |- *. rewrite <- HR. reflexivity.
Qed.

Lemma final_program_reader_sem {E : Type}
    (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Unit + Word32)) (environment : E) :
  final_program op tt environment =
    option_bind (fun result : tySem (Bit + Unit) =>
        match result with inl x => Some x | inr _ => Some Bit.one end)
      (for_while_run 5 (final_step (fun w => op w environment)) tt tt).
Proof.
  rewrite final_program_reader_finish.
  rewrite for_while_program_reader_sem.
  assert (HBody : for_while_run 5 (fun p => final_body op p environment) tt tt =
    for_while_run 5 (final_step (fun w => op w environment)) tt tt).
  { apply for_while_run_ext. intro p. apply final_body_reader_sem. }
  rewrite HBody. reflexivity.
Qed.

Local Open Scope Z_scope.

Lemma final_tail_value (v : tySem Word32) :
  |[final_tail]| v =
    if predicate_numeric 5 Datatypes.true (wz 5 v) then inr tt else inl Bit.zero.
Proof.
  unfold wz. rewrite <- predicate_spec_numeric.
  assert (Hs : |[final_tail]| v =
    match @predicate_spec 5 Datatypes.true CoreFunSem v with
    | inl _ => inl Bit.zero | inr _ => inr tt end).
  { unfold final_tail. cbn -[predicate_spec].
    destruct (@predicate_spec 5 Datatypes.true CoreFunSem v) as [ [] | [] ]; reflexivity. }
  rewrite Hs.
  destruct (@predicate_spec 5 Datatypes.true CoreFunSem v) as [ [] | [] ]; reflexivity.
Qed.

(** Length of the longest prefix whose elements all satisfy [f]. *)
Fixpoint lead {X : Type} (f : X -> bool) (xs : list X) : nat :=
  match xs with
  | x :: t => if f x then S (lead f t) else 0%nat
  | [] => 0%nat
  end.

Lemma lead_le {X : Type} (f : X -> bool) xs : (lead f xs <= length xs)%nat.
Proof. induction xs as [|x t IH]; cbn; [lia|destruct (f x); lia]. Qed.

Lemma lead_before {X : Type} (f : X -> bool) xs i :
  (i < lead f xs)%nat -> exists x, nth_error xs i = Some x /\ f x = Datatypes.true.
Proof.
  revert i. induction xs as [|x t IH]; intros i Hi; cbn in Hi; [lia|].
  destruct (f x) eqn:Hf; [|lia].
  destruct i as [|i]; [exists x; split; [reflexivity|exact Hf] |].
  apply IH. lia.
Qed.

Lemma lead_at {X : Type} (f : X -> bool) xs :
  match nth_error xs (lead f xs) with
  | None => forallb f xs = Datatypes.true
  | Some x => f x = Datatypes.false /\ forallb f xs = Datatypes.false
  end.
Proof.
  induction xs as [|x t IH]; cbn; [reflexivity|].
  destruct (f x) eqn:Hf; cbn; [|rewrite Hf; split; reflexivity].
  destruct (nth_error t (lead f t)); [destruct IH; split; assumption|exact IH].
Qed.

Lemma final_run_list {X : Type} (xs : list X) (enc : X -> tySem Word32) (f : X -> bool)
    (op : tySem Word32 -> option (tySem (Unit + Word32))) :
  Z.of_nat (length xs) < wsize 5 ->
  (forall x, predicate_numeric 5 Datatypes.true (wz 5 (enc x)) = f x) ->
  (forall w, op w = Some (match nth_error xs (Z.to_nat (wz 5 w)) with
                          | Some x => inr (enc x) | None => inl tt end)) ->
  for_while_run 5 (final_step op) tt tt = Some (inl (Bit.fromBool (forallb f xs))).
Proof.
  intros Hlen Hf Hop.
  pose proof (lead_le f xs) as Hle.
  refine (@for_while_run_seq_left Unit Bit Unit (fun _ : Z => tt) 5 0 (Z.of_nat (lead f xs))
    (Bit.fromBool (forallb f xs)) (final_step op) tt _ _ _).
  - lia.
  - intros w Hw. unfold final_step. cbn [fst snd]. rewrite Hop.
    destruct (@lead_before X f xs (Z.to_nat (wz 5 w))) as (x & Hx & Hfx).
    { pose proof (wz_range 5 w). lia. }
    rewrite Hx, final_tail_value, Hf, Hfx. reflexivity.
  - intros w Hw. unfold final_step. cbn [fst snd]. rewrite Hop.
    assert (Hi : Z.to_nat (wz 5 w) = lead f xs) by lia.
    rewrite Hi. pose proof (lead_at f xs) as Hat.
    destruct (nth_error xs (lead f xs)) as [x|].
    + destruct Hat as [Hfx Hall]. rewrite final_tail_value, Hf, Hfx, Hall. reflexivity.
    + rewrite Hat. reflexivity.
Qed.

Definition sequence_final (txi : sigTxInput) : bool :=
  Z.eqb (Int.unsigned (sigTxiSequence txi)) 4294967295.

Definition bitcoin_tx_is_final_spec {alg : Primitive.Algebra} : alg Ty.Unit Bit :=
  final_program (Primitive.Combinators.prim Bitcoin.InputSequence).

Lemma bitcoin_tx_is_final_spec_parametric : Primitive.Parametric (@bitcoin_tx_is_final_spec).
Proof.
  intros alg1 alg2 [R [HA HP]]. unfold bitcoin_tx_is_final_spec.
  apply (final_program_parametric (Alg.Core.Parametric.Pack (Alg.Assertion.Parametric.base HA))).
  apply (prim_Parametric (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma sequence_final_numeric (txi : sigTxInput) :
  predicate_numeric 5 Datatypes.true
    (wz 5 (@fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi)))) = sequence_final txi.
Proof.
  unfold wz, sequence_final, predicate_numeric.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  rewrite Z.mod_small by exact (Int.unsigned_range (sigTxiSequence txi)).
  reflexivity.
Qed.

Lemma final_list_op (xs : list sigTxInput) (w : tySem Word32) :
  Some (match option_map (fun txi => @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi)))
                (nth_error xs (Z.to_nat (@toZ (WordToZ 5) w))) with
        | Some b => inr b | None => inl tt end : tySem (Ty.Sum Ty.Unit Word32)) =
  Some (match nth_error xs (Z.to_nat (wz 5 w)) with
        | Some x => inr (@fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence x))) | None => inl tt end).
Proof. unfold wz. destruct (nth_error xs (Z.to_nat (@toZ (WordToZ 5) w))); reflexivity. Qed.

Lemma bitcoin_tx_is_final_spec_value (environment : Bitcoin.env) :
  @bitcoin_tx_is_final_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (Bit.fromBool (forallb sequence_final (sigTxIn (Bitcoin.envTx environment)))).
Proof.
  unfold bitcoin_tx_is_final_spec.
  change (final_program
    (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word32)
      (PrimitivePrimSem option_Monad_Zero) Bitcoin.InputSequence :
      CoreSem (ReaderT_CIMonad Bitcoin.env option_CIMonad) Word32 (Ty.Sum Ty.Unit Word32))
    tt environment =
    Some (Bit.fromBool (forallb sequence_final (sigTxIn (Bitcoin.envTx environment))))).
  rewrite final_program_reader_sem.
  rewrite (@final_run_list _ (sigTxIn (Bitcoin.envTx environment))
    (fun txi => @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi))) sequence_final).
  - reflexivity.
  - pose proof (sigTxInBounds (Bitcoin.envTx environment)) as HBound.
    rewrite Zlength_correct in HBound. exact (proj2 HBound).
  - exact sequence_final_numeric.
  - intro w. exact (final_list_op (sigTxIn (Bitcoin.envTx environment)) w).
Qed.

(** Literal Transaction.totalInputValue / totalOutputValue: a [forWhile] loop
    over the Word32 counters summing InputValue / OutputValue until the first
    out-of-range counter.  Semantic reduction to the list sum. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq C.jet_word_repr.
Import ListNotations.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.
Set Implicit Arguments.
Set Default Timeout 60.

Definition total_adder {alg : Core.Algebra} : alg (Word 6 * Word 6) (Word 6) := adder >>> I H.

Definition total_body {alg : Core.Algebra} (op : alg Word32 (Unit + Word64)) :
    alg ((Unit * Word 5) * Word 6) (Word 6 + Word 6) :=
  (take (drop op) &&& (I H)) >>> case (injl (I H)) (injr total_adder).

Definition total_program {alg : Core.Algebra} (op : alg Word32 (Unit + Word64)) : alg Unit (Word 6) :=
  (iden &&& zero) >>> for_while_program 5 (total_body op) >>> copair iden iden.

Lemma total_adder_parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2) :
  R _ _ total_adder total_adder.
Proof. unfold total_adder. auto 12 with parametricity. Qed.
#[local] Hint Resolve total_adder_parametric : parametricity.

Lemma total_body_parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
    (op1 : alg1 Word32 (Unit + Word64)) (op2 : alg2 Word32 (Unit + Word64)) :
  R _ _ op1 op2 -> R _ _ (total_body op1) (total_body op2).
Proof. intro HO. unfold total_body. auto 12 with parametricity. Qed.

Lemma total_program_parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
    (op1 : alg1 Word32 (Unit + Word64)) (op2 : alg2 Word32 (Unit + Word64)) :
  R _ _ op1 op2 -> R _ _ (total_program op1) (total_program op2).
Proof.
  intro HO. unfold total_program.
  apply comp_Parametric; [auto with parametricity|].
  apply comp_Parametric; [|auto with parametricity].
  apply for_while_program_parametric. apply total_body_parametric. exact HO.
Qed.

Definition total_step (op : tySem Word32 -> option (tySem (Unit + Word64)))
    (p : tySem ((Unit * Word 5) * Word 6)) : option (tySem (Word 6 + Word 6)) :=
  match op (snd (fst p)) with
  | None => None
  | Some (inl _) => Some (inl (snd p))
  | Some (inr v) => Some (inr (|[total_adder]| (v, snd p)))
  end.

Lemma total_adder_core_parametric : Core.Parametric (fun term => @total_adder term).
Proof. intros alg1 alg2 R. apply total_adder_parametric. Qed.

Lemma total_adder_reader_sem {E : Type} (x : tySem (Word 6 * Word 6)) (environment : E) :
  @total_adder (CoreSem (ReaderT_CIMonad E option_CIMonad)) x environment =
    Some (|[total_adder]| x).
Proof.
  pose proof (@CoreSem_initial (ReaderT_CIMonad E option_CIMonad) _ _
    (fun term => @total_adder term) total_adder_core_parametric x) as Hs.
  refine (eq_trans (f_equal (fun f => f environment) Hs) _). reflexivity.
Qed.

Lemma total_body_reader_sem {E : Type} (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Unit + Word64))
    (p : tySem ((Unit * Word 5) * Word 6)) (environment : E) :
  total_body op p environment = total_step (fun w => op w environment) p.
Proof.
  destruct p as [[[] w] acc]. unfold total_body, total_step.
  destruct (op w environment) as [[a | b] | ] eqn:HO.
  - lazy beta iota zeta delta -[total_adder] in HO |- *. rewrite HO. reflexivity.
  - lazy beta iota zeta delta -[total_adder] in HO |- *. rewrite HO.
    assert (Hadd : ltac:(let t := eval lazy beta iota zeta delta -[total_adder] in
      (@total_adder (CoreSem (ReaderT_CIMonad E option_CIMonad)) (b, acc) environment) in
      exact (t = Some (|[total_adder]| (b, acc))))) by exact (total_adder_reader_sem (b, acc) environment).
    rewrite Hadd. reflexivity.
  - lazy beta iota zeta delta -[total_adder] in HO |- *. rewrite HO. reflexivity.
Qed.

Lemma zero_core_parametric n : Core.Parametric (fun term => @zero n term).
Proof. intros alg1 alg2 R. apply zero_Parametric. Qed.

Lemma total_program_reader_finish {E : Type}
    (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Unit + Word64)) (environment : E) :
  total_program op tt environment =
    option_bind (fun result : tySem (Word 6 + Word 6) => match result with inl x => Some x | inr x => Some x end)
      (@for_while_program 5 Unit (Word 6) (Word 6) (CoreSem (ReaderT_CIMonad E option_CIMonad))
        (total_body op) (tt, |[zero (n := 6)]| tt) environment).
Proof.
  unfold total_program.
  remember (@for_while_program 5 Unit (Word 6) (Word 6) (CoreSem (ReaderT_CIMonad E option_CIMonad))
        (total_body op) (tt, |[zero (n := 6)]| tt) environment) as result eqn:HR.
  destruct result as [[x | x] | ].
  - lazy beta iota zeta delta -[for_while_program total_body] in HR |- *. rewrite <- HR. reflexivity.
  - lazy beta iota zeta delta -[for_while_program total_body] in HR |- *. rewrite <- HR. reflexivity.
  - lazy beta iota zeta delta -[for_while_program total_body] in HR |- *. rewrite <- HR. reflexivity.
Qed.

Lemma total_program_reader_sem {E : Type}
    (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Unit + Word64)) (environment : E) :
  total_program op tt environment =
    option_bind (fun result : tySem (Word 6 + Word 6) => match result with inl x => Some x | inr x => Some x end)
      (for_while_run 5 (total_step (fun w => op w environment)) tt (|[zero (n := 6)]| tt)).
Proof.
  rewrite total_program_reader_finish.
  rewrite for_while_program_reader_sem.
  assert (HBody : for_while_run 5 (fun p => total_body op p environment) tt (|[zero (n := 6)]| tt) =
    for_while_run 5 (total_step (fun w => op w environment)) tt (|[zero (n := 6)]| tt)).
  { apply for_while_run_ext. intro p. apply total_body_reader_sem. }
  rewrite HBody. reflexivity.
Qed.

Local Open Scope Z_scope.

Definition fw6 (z : Z) : tySem (Word 6) := @fromZ (WordToZ 6) z.

Lemma fw6_toZ z : wz 6 (fw6 z) = z mod wsize 6.
Proof.
  unfold wz, fw6, wsize. rewrite to_fromZ, two_power_nat_equiv, word_bitSize. reflexivity.
Qed.

Lemma adder_balance (a b : Word64) (c : Bit) (w : Word64) :
  |[ @adder 6 CoreFunSem ]| (a, b) = (c, w) ->
  toZ c * wsize 6 + wz 6 w = wz 6 a + wz 6 b.
Proof.
  intro Hr.
  pose proof (adder_correct 6 a b) as Hc. rewrite Hr in Hc.
  rewrite (@toZ_Pair BitToZ (WordToZ 6)) in Hc.
  rewrite two_power_nat_equiv, word_bitSize in Hc.
  exact Hc.
Qed.

Lemma total_adder_fromZ x y : |[total_adder]| (fw6 x, fw6 y) = fw6 (x + y).
Proof.
  assert (Hs : |[total_adder]| (fw6 x, fw6 y) = snd (|[ @adder 6 CoreFunSem ]| (fw6 x, fw6 y)))
    by reflexivity.
  rewrite Hs. clear Hs.
  destruct (|[ @adder 6 CoreFunSem ]| (fw6 x, fw6 y)) as [c w] eqn:Hr.
  pose proof (adder_balance Hr) as Hc.
  pose proof (wz_range 6 w) as Hw. pose proof (wsize_pos 6) as Hpos.
  rewrite (fw6_toZ x), (fw6_toZ y) in Hc.
  assert (Hsum : (x + y) mod wsize 6 = wz 6 w).
  { rewrite Z.add_mod by lia.
    assert (HZ : x mod wsize 6 + y mod wsize 6 = toZ c * wsize 6 + wz 6 w) by lia.
    rewrite HZ. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. exact Hw. }
  cbn [snd]. unfold fw6. rewrite <- (word_fromZ_mod 6 (x + y)).
  change (2 ^ Z.of_nat (Nat.pow 2 6)) with (wsize 6). rewrite Hsum.
  unfold wz. symmetry. apply from_toZ.
Qed.

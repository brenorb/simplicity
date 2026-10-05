(** Canonical Transaction.totalInputValue / totalOutputValue programs over the
    Bitcoin primitives, and their value: the sum of the environment's input /
    output amounts.  No C execution is claimed here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import Simplicity.Util.Option Simplicity.Util.List Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq C.jet_word_repr C.jet_bitcoin_totals_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition bitcoin_total_input_value_spec {alg : Primitive.Algebra} : alg Ty.Unit Word64 :=
  total_program (Primitive.Combinators.prim Bitcoin.InputValue).
Definition bitcoin_total_output_value_spec {alg : Primitive.Algebra} : alg Ty.Unit Word64 :=
  total_program (Primitive.Combinators.prim Bitcoin.OutputValue).

Lemma bitcoin_total_input_value_spec_parametric :
  Primitive.Parametric (@bitcoin_total_input_value_spec).
Proof.
  intros alg1 alg2 [R [HA HP]]. unfold bitcoin_total_input_value_spec.
  apply (total_program_parametric (Alg.Core.Parametric.Pack (Alg.Assertion.Parametric.base HA))).
  apply (prim_Parametric (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma bitcoin_total_output_value_spec_parametric :
  Primitive.Parametric (@bitcoin_total_output_value_spec).
Proof.
  intros alg1 alg2 [R [HA HP]]. unfold bitcoin_total_output_value_spec.
  apply (total_program_parametric (Alg.Core.Parametric.Pack (Alg.Assertion.Parametric.base HA))).
  apply (prim_Parametric (Primitive.Parametric.Pack (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma total_list_op {X : Type} (xs : list X) (f : X -> Z) (w : tySem Word32) :
  Some (match option_map (fun x => fw6 (f x)) (nth_error xs (Z.to_nat (@toZ (WordToZ 5) w))) with
        | Some b => inr b | None => inl tt end : tySem (Ty.Sum Ty.Unit Word64)) =
  Some (match nth_error (map f xs) (Z.to_nat (wz 5 w)) with
        | Some v => inr (fw6 v) | None => inl tt end).
Proof.
  unfold wz. rewrite nth_error_map.
  destruct (nth_error xs (Z.to_nat (@toZ (WordToZ 5) w))); reflexivity.
Qed.

Lemma bitcoin_total_input_value_spec_sum (environment : Bitcoin.env) :
  @bitcoin_total_input_value_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (fw6 (sigTxTotalInValue (Bitcoin.envTx environment))).
Proof.
  unfold bitcoin_total_input_value_spec.
  change (total_program
    (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word64)
      (PrimitivePrimSem option_Monad_Zero) Bitcoin.InputValue :
      CoreSem (ReaderT_CIMonad Bitcoin.env option_CIMonad) Word32 (Ty.Sum Ty.Unit Word64))
    tt environment = Some (fw6 (sigTxTotalInValue (Bitcoin.envTx environment)))).
  rewrite total_program_reader_sem.
  rewrite (@total_run_vals
    (map (fun i => Int64.signed (sigTxiValue i)) (sigTxIn (Bitcoin.envTx environment)))).
  - reflexivity.
  - rewrite map_length.
    pose proof (sigTxInBounds (Bitcoin.envTx environment)) as HBound.
    rewrite Zlength_correct in HBound. exact (proj2 HBound).
  - intro w.
    exact (total_list_op (sigTxIn (Bitcoin.envTx environment))
      (fun i => Int64.signed (sigTxiValue i)) w).
Qed.

Lemma bitcoin_total_output_value_spec_sum (environment : Bitcoin.env) :
  @bitcoin_total_output_value_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (fw6 (sigTxTotalOutValue (Bitcoin.envTx environment))).
Proof.
  unfold bitcoin_total_output_value_spec.
  change (total_program
    (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word64)
      (PrimitivePrimSem option_Monad_Zero) Bitcoin.OutputValue :
      CoreSem (ReaderT_CIMonad Bitcoin.env option_CIMonad) Word32 (Ty.Sum Ty.Unit Word64))
    tt environment = Some (fw6 (sigTxTotalOutValue (Bitcoin.envTx environment)))).
  rewrite total_program_reader_sem.
  rewrite (@total_run_vals
    (map (fun i => Int64.signed (txoValue i)) (sigTxOut (Bitcoin.envTx environment)))).
  - reflexivity.
  - rewrite map_length.
    pose proof (sigTxOutBounds (Bitcoin.envTx environment)) as HBound.
    rewrite Zlength_correct in HBound. exact (proj2 HBound).
  - intro w.
    exact (total_list_op (sigTxOut (Bitcoin.envTx environment))
      (fun i => Int64.signed (txoValue i)) w).
Qed.

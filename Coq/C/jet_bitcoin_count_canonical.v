(** Current canonical Transaction.numInputs/numOutputs programs.
    Unlike the legacy Coq count primitives, these are literal firstFail searches
    over InputValue/OutputValue. No C execution/coverage is claimed here. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import Simplicity.Primitive.Bitcoin Simplicity.Util.Option.
Require Import C.jet_firstFail_spec.
Set Default Timeout 10.

Definition bitcoin_transaction_num_inputs_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  first_fail_program 5 (Primitive.Combinators.prim Bitcoin.InputValue).
Definition bitcoin_transaction_num_outputs_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  first_fail_program 5 (Primitive.Combinators.prim Bitcoin.OutputValue).

Lemma bitcoin_transaction_num_inputs_spec_parametric :
  Primitive.Parametric (@bitcoin_transaction_num_inputs_spec).
Proof.
  intros alg1 alg2 [R [HA HP]]. unfold bitcoin_transaction_num_inputs_spec.
  apply (first_fail_program_parametric 5 (Alg.Assertion.Parametric.Pack HA)).
  apply (prim_Parametric (Primitive.Parametric.Pack
    (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma bitcoin_transaction_num_outputs_spec_parametric :
  Primitive.Parametric (@bitcoin_transaction_num_outputs_spec).
Proof.
  intros alg1 alg2 [R [HA HP]]. unfold bitcoin_transaction_num_outputs_spec.
  apply (first_fail_program_parametric 5 (Alg.Assertion.Parametric.Pack HA)).
  apply (prim_Parametric (Primitive.Parametric.Pack
    (Primitive.Parametric.Build_class HA HP))).
Qed.

Lemma bitcoin_transaction_num_inputs_spec_search (environment : Bitcoin.env) :
  @bitcoin_transaction_num_inputs_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    first_fail_run 5 (fun w => Bitcoin.sem Bitcoin.InputValue w environment).
Proof.
  unfold bitcoin_transaction_num_inputs_spec.
  change (first_fail_program 5
    (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word64)
      (PrimitivePrimSem option_Monad_Zero) Bitcoin.InputValue :
      Alg.AssertionSem (Monad.Reader.ReaderT_CIMonadZero Bitcoin.env option_Monad_Zero)
        Word32 (Ty.Sum Ty.Unit Word64)) tt environment =
      first_fail_run 5 (fun w => Bitcoin.sem Bitcoin.InputValue w environment)).
  rewrite first_fail_program_reader_sem. reflexivity.
Qed.

Lemma bitcoin_transaction_num_outputs_spec_search (environment : Bitcoin.env) :
  @bitcoin_transaction_num_outputs_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    first_fail_run 5 (fun w => Bitcoin.sem Bitcoin.OutputValue w environment).
Proof.
  unfold bitcoin_transaction_num_outputs_spec.
  change (first_fail_program 5
    (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word64)
      (PrimitivePrimSem option_Monad_Zero) Bitcoin.OutputValue :
      Alg.AssertionSem (Monad.Reader.ReaderT_CIMonadZero Bitcoin.env option_Monad_Zero)
        Word32 (Ty.Sum Ty.Unit Word64)) tt environment =
      first_fail_run 5 (fun w => Bitcoin.sem Bitcoin.OutputValue w environment)).
  rewrite first_fail_program_reader_sem. reflexivity.
Qed.

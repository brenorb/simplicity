(** Literal Bitcoin count searches compute the environment's bounded list lengths.
    This bridge is not, by itself, a proof of the C count jets. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Primitive.Bitcoin.
Require Import Simplicity.Util.Option C.jet_bitcoin_count_canonical C.jet_firstFail_list.
Require Import C.jet_firstFail_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma bitcoin_transaction_num_inputs_spec_length (environment : Bitcoin.env) :
  @bitcoin_transaction_num_inputs_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (@fromZ (WordToZ 5) (Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))))).
Proof.
  rewrite bitcoin_transaction_num_inputs_spec_search.
  change (first_fail_run 5
    (indexed_list_primitive 5 (sigTxIn (Bitcoin.envTx environment))
      (fun txi => @fromZ (WordToZ 6) (Int64.signed (sigTxiValue txi)))) =
    Some (@fromZ (WordToZ 5) (Z.of_nat (length (sigTxIn (Bitcoin.envTx environment)))))).
  apply first_fail_list_count.
  pose proof (sigTxInBounds (Bitcoin.envTx environment)) as HBound.
  rewrite Zlength_correct in HBound.
  change (0 < Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) < 4294967296) in HBound.
  change (Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) < 4294967296). lia.
Qed.

Lemma bitcoin_transaction_num_outputs_spec_length (environment : Bitcoin.env) :
  @bitcoin_transaction_num_outputs_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (@fromZ (WordToZ 5) (Z.of_nat (length (sigTxOut (Bitcoin.envTx environment))))).
Proof.
  rewrite bitcoin_transaction_num_outputs_spec_search.
  change (first_fail_run 5
    (indexed_list_primitive 5 (sigTxOut (Bitcoin.envTx environment))
      (fun txout => @fromZ (WordToZ 6) (Int64.signed (txoValue txout)))) =
    Some (@fromZ (WordToZ 5) (Z.of_nat (length (sigTxOut (Bitcoin.envTx environment)))))).
  apply first_fail_list_count.
  pose proof (sigTxOutBounds (Bitcoin.envTx environment)) as HBound.
  rewrite Zlength_correct in HBound.
  change (0 < Z.of_nat (length (sigTxOut (Bitcoin.envTx environment))) < 4294967296) in HBound.
  change (Z.of_nat (length (sigTxOut (Bitcoin.envTx environment))) < 4294967296). lia.
Qed.

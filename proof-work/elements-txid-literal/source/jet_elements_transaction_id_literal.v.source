(** Whole-C transaction_id getter, reusing the checked digest conversion.
    The serialization/hash value is the existing Elements primitive port's
    [txid]. Canonical source correspondence for that serialization is a
    separate review obligation; this module does not establish the C
    environment constructor's cached transaction identifier. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_elements_hash_field_jets C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local.
Require Import C.jet_elements_sequence_literal C.jet_elements_hash_literal C.jet_haskell_hash_word.
Set Default Timeout 10.
Local Open Scope Z_scope.

Definition elements_transaction_id_literal_spec :=
  elements_hash_literal_spec (fun e => txid (Elements.envTx e)).

Lemma elements_transaction_id_literal_matches a environment :
  @elements_transaction_id_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_transaction_id_literal_spec a environment.
Proof.
  destruct a.
  change (Some (from_hash256 (txid (Elements.envTx environment))) =
    elements_transaction_id_literal_spec tt environment).
  unfold elements_transaction_id_literal_spec, elements_hash_literal_spec.
  f_equal. symmetry. apply haskell_hash_word256.
Qed.

Theorem elements_transaction_id_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_transaction_id elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => txid (Elements.envTx e)) 0 664 760)
    elements_transaction_id_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_transaction_id_literal_matches | exact elements_transaction_id_local_spec].
Qed.

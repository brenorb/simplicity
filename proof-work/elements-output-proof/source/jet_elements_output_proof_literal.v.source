(** Actual C output proof-hash getters, reusing the shared indexed conversion.
    Explicit values have an empty proof view, not an absent output. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal C.jet_haskell_hash_word.
Require Import C.jet_haskell_word_conversion.
Require Import C.jet_elements_indexed_ptr C.jet_elements_output_proof_jets.
Require Import C.jet_elements_indexed_literal C.jet_uint32_array_init.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition haskell_confidential_proof_view {A : Set} (c : confidential (list byte) A) : list byte :=
  match c with Explicit _ => [] | Confidential _ proof => proof end.

Lemma haskell_confidential_proof_view_matches {A : Set} (c : confidential (list byte) A) :
  viewPrf c = haskell_confidential_proof_view c.
Proof. reflexivity. Qed.

Definition elements_output_proof_digest_literal_spec (proof_of : txOutput -> list byte) :=
  elements_indexed_literal_result (fun e => sigTxOut (Elements.envTx e))
    (fun txo => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (byteStringHash (proof_of txo))))).

Lemma elements_output_proof_digest_literal_matches proof_of a environment :
  Some (match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
        | None => inl tt | Some txo => inr (from_hash256 (byteStringHash (proof_of txo))) end) =
    elements_output_proof_digest_literal_spec proof_of a environment.
Proof.
  unfold elements_output_proof_digest_literal_spec.
  apply (@elements_indexed_literal_matches Elements.env txOutput Word256
    (fun e => sigTxOut (Elements.envTx e)) (fun txo => from_hash256 (byteStringHash (proof_of txo)))
    (fun txo => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (byteStringHash (proof_of txo)))))).
  intros txo. symmetry. apply haskell_hash_word256.
Qed.

Definition elements_output_surjection_proof_literal_spec :=
  elements_output_proof_digest_literal_spec (fun txo => haskell_confidential_proof_view (txoAsset txo)).

Lemma elements_output_surjection_proof_literal_matches a environment :
  @elements_output_surjection_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_surjection_proof_literal_spec a environment.
Proof.
  rewrite elements_output_surjection_proof_sem.
  unfold elements_output_surjection_proof_result, elements_output_surjection_proof_literal_spec.
  rewrite <- elements_output_proof_digest_literal_matches.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|];
    [rewrite haskell_confidential_proof_view_matches|]; reflexivity.
Qed.

Definition elements_output_range_proof_literal_spec :=
  elements_output_proof_digest_literal_spec (fun txo => haskell_confidential_proof_view (txoAmount txo)).

Lemma elements_output_range_proof_literal_matches a environment :
  @elements_output_range_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_range_proof_literal_spec a environment.
Proof.
  rewrite elements_output_range_proof_sem.
  unfold elements_output_range_proof_result, elements_output_range_proof_literal_spec.
  rewrite <- elements_output_proof_digest_literal_matches.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|];
    [rewrite haskell_confidential_proof_view_matches|]; reflexivity.
Qed.

Theorem elements_output_surjection_proof_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_surjection_proof elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (surjection_proof_hash_words txo)) 248 36 8 704)
    elements_output_surjection_proof_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_output_surjection_proof_literal_matches|exact elements_output_surjection_proof_local_spec].
Qed.

Theorem elements_output_range_proof_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_range_proof elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (range_proof_hash_words txo)) 248 68 8 704)
    elements_output_range_proof_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_output_range_proof_literal_matches|exact elements_output_range_proof_local_spec].
Qed.

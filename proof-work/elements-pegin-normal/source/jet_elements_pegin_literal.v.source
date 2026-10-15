(** Actual indexed/current pegin C jets, retaining both presence tags and
    literal Haskell index and digest decoding. No hashing is done by these jets. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word.
Require Import C.jet_elements_pegin_local C.jet_elements_current_gen C.jet_elements_current_gen_jets.
Require Import C.jet_elements_current_sequence_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_input_pegin_literal_spec (a : tySem Word32) (environment : Elements.env) :
    option (tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))) :=
  Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | None => inl tt
        | Some txi => inr (match sigTxiPegin txi with
            | None => inl tt
            | Some h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
            end)
        end).

Lemma elements_input_pegin_literal_matches a environment :
  @elements_input_pegin_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_pegin_literal_spec a environment.
Proof.
  rewrite elements_input_pegin_hash_sem.
  unfold elements_input_pegin_literal_spec, elements_pegin_result, elements_pegin_hashes.
  rewrite haskell_from_word_matches, nth_error_map.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|];
    [|reflexivity].
  cbv beta iota delta [Datatypes.option_map].
  destruct (sigTxiPegin txi) as [h|]; [rewrite haskell_hash_word256|]; reflexivity.
Qed.

Definition elements_current_pegin_literal_spec :=
  elements_current_literal_result elements_input_pegin_literal_spec.

Lemma elements_current_pegin_literal_matches a environment :
  @elements_current_pegin_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_pegin_literal_spec a environment.
Proof.
  unfold elements_current_pegin_spec, elements_current_pegin_literal_spec.
  apply elements_current_literal_sem. exact elements_input_pegin_literal_matches.
Qed.

Theorem elements_input_pegin_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_pegin elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) elements_input_pegin_hash_env_rep
    elements_input_pegin_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_pegin_literal_matches|exact elements_input_pegin_hash_local_spec].
Qed.

Theorem elements_current_pegin_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_pegin elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep sigTxiPegin 537 32) 544 0 696)
    elements_current_pegin_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_pegin_literal_matches|exact elements_current_pegin_local_spec].
Qed.

Print Assumptions elements_input_pegin_literal_matches.
Print Assumptions elements_current_pegin_literal_matches.
Print Assumptions elements_input_pegin_literal_local_spec.
Print Assumptions elements_current_pegin_literal_local_spec.

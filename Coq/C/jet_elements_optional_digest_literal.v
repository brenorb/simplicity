(** Shared optional-digest conversion, used by the actual indexed/current
    annex-hash C jets. Both presence tags distinguish an invalid input index,
    an absent annex, and a present annex (including the empty byte string). *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word.
Require Import C.jet_elements_annex_local C.jet_elements_current_gen C.jet_elements_current_gen_jets.
Require Import C.jet_elements_current_sequence_literal C.jet_elements_pegin_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_input_optional_digest_literal_spec (hash_of : sigTxInput -> option hash256)
    (a : tySem Word32) (environment : Elements.env) : option (tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))) :=
  Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | None => inl tt
        | Some txi => inr (match hash_of txi with
            | None => inl tt
            | Some h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
            end)
        end).

Lemma elements_input_optional_digest_literal_matches hash_of a environment :
  Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a)) with
        | None => inl tt
        | Some txi => inr (match hash_of txi with None => inl tt | Some h => inr (from_hash256 h) end)
        end) = elements_input_optional_digest_literal_spec hash_of a environment.
Proof.
  unfold elements_input_optional_digest_literal_spec. rewrite haskell_from_word_matches.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  destruct (hash_of txi) as [h|]; [rewrite haskell_hash_word256|]; reflexivity.
Qed.

Lemma elements_pegin_literal_uses_optional_digest a environment :
  elements_input_pegin_literal_spec a environment =
    elements_input_optional_digest_literal_spec sigTxiPegin a environment.
Proof. reflexivity. Qed.

Definition elements_input_annex_hash_literal_spec :=
  elements_input_optional_digest_literal_spec (fun txi => option_map byteStringHash (sigTxiAnnex txi)).

Lemma elements_input_annex_hash_literal_matches a environment :
  @elements_input_annex_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_annex_hash_literal_spec a environment.
Proof.
  rewrite elements_input_annex_hash_sem.
  unfold elements_annex_result, elements_annex_hashes, elements_input_annex_hash_literal_spec.
  rewrite nth_error_map. rewrite <- elements_input_optional_digest_literal_matches.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  cbv beta iota delta [Datatypes.option_map].
  destruct (sigTxiAnnex txi); reflexivity.
Qed.

Definition elements_current_annex_hash_literal_spec :=
  elements_current_literal_result elements_input_annex_hash_literal_spec.

Lemma elements_current_annex_hash_literal_matches a environment :
  @elements_current_annex_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_annex_hash_literal_spec a environment.
Proof.
  unfold elements_current_annex_hash_spec, elements_current_annex_hash_literal_spec.
  apply elements_current_literal_sem. exact elements_input_annex_hash_literal_matches.
Qed.

Theorem elements_input_annex_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_annex_hash elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) elements_input_annex_hash_env_rep
    elements_input_annex_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_annex_hash_literal_matches|exact elements_input_annex_hash_local_spec].
Qed.

Theorem elements_current_annex_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_annex_hash elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep annex_hash_of 536 0) 544 0 696)
    elements_current_annex_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_annex_hash_literal_matches|exact elements_current_annex_hash_local_spec].
Qed.

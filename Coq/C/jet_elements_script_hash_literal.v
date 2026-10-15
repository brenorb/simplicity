(** Actual indexed/current script-hash C jets with literal index/digest
    conversions. The initial environment represents the specified cached
    digest; these jets copy it, not compute SHA-256 themselves. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word.
Require Import C.jet_elements_input_hash_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_ptr_jets C.jet_uint32_array_init.
Require Import C.jet_elements_current_sequence_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_input_digest_literal_spec (hash_of : sigTxInput -> hash256)
    (a : tySem Word32) (environment : Elements.env) : option (tySem (Ty.Sum Ty.Unit Word256)) :=
  Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | None => inl tt
        | Some txi => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (hash_of txi))))
        end).

Lemma elements_input_digest_literal_matches hash_of a environment :
  Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a)) with
        | None => inl tt | Some txi => inr (from_hash256 (hash_of txi)) end) =
    elements_input_digest_literal_spec hash_of a environment.
Proof.
  unfold elements_input_digest_literal_spec. rewrite haskell_from_word_matches.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|];
    [rewrite haskell_hash_word256|]; reflexivity.
Qed.

Definition elements_input_script_hash_literal_spec :=
  elements_input_digest_literal_spec (fun txi => byteStringHash (utxo_script_bytes txi)).

Definition elements_input_script_sig_hash_literal_spec :=
  elements_input_digest_literal_spec (fun txi => byteStringHash (sigTxiScriptSig txi)).

Lemma elements_input_script_hash_literal_matches a environment :
  @elements_input_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_script_hash_literal_spec a environment.
Proof.
  rewrite elements_input_script_hash_sem.
  unfold elements_input_script_hash_result, elements_input_script_hash_literal_spec.
  apply elements_input_digest_literal_matches.
Qed.

Lemma elements_input_script_sig_hash_literal_matches a environment :
  @elements_input_script_sig_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_script_sig_hash_literal_spec a environment.
Proof.
  rewrite elements_input_script_sig_hash_sem.
  unfold elements_input_script_sig_hash_result, elements_input_script_sig_hash_literal_spec.
  apply elements_input_digest_literal_matches.
Qed.

Definition elements_current_script_hash_literal_spec :=
  elements_current_literal_result elements_input_script_hash_literal_spec.

Definition elements_current_script_sig_hash_literal_spec :=
  elements_current_literal_result elements_input_script_sig_hash_literal_spec.

Lemma elements_current_script_hash_literal_matches a environment :
  @elements_current_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_script_hash_literal_spec a environment.
Proof.
  unfold elements_current_script_hash_spec, elements_current_script_hash_literal_spec.
  apply elements_current_literal_sem. exact elements_input_script_hash_literal_matches.
Qed.

Lemma elements_current_script_sig_hash_literal_matches a environment :
  @elements_current_script_sig_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_script_sig_hash_literal_spec a environment.
Proof.
  unfold elements_current_script_sig_hash_spec, elements_current_script_sig_hash_literal_spec.
  apply elements_current_literal_sem. exact elements_input_script_sig_hash_literal_matches.
Qed.

Theorem elements_input_script_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_script_hash elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => uint32_array_at m b ofs (utxo_script_hash_words txi)) 544 136 0 696)
    elements_input_script_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_script_hash_literal_matches|exact elements_input_script_hash_local_spec].
Qed.

Theorem elements_input_script_sig_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_script_sig_hash elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => uint32_array_at m b ofs (script_sig_hash_words txi)) 544 64 0 696)
    elements_input_script_sig_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_script_sig_hash_literal_matches|exact elements_input_script_sig_hash_local_spec].
Qed.

Theorem elements_current_script_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_script_hash elements_ge Elements.env Ty.Unit Word256
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx
      (fun m b ofs txi => uint32_array_at m b ofs (utxo_script_hash_words txi)) 544 136 0 696)
    elements_current_script_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_script_hash_literal_matches|exact elements_current_script_hash_local_spec].
Qed.

Theorem elements_current_script_sig_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_script_sig_hash elements_ge Elements.env Ty.Unit Word256
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx
      (fun m b ofs txi => uint32_array_at m b ofs (script_sig_hash_words txi)) 544 64 0 696)
    elements_current_script_sig_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_script_sig_hash_literal_matches|exact elements_current_script_sig_hash_local_spec].
Qed.

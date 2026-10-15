(** Four actual C issuance-proof digest getters. All in-range inputs have a
    digest, including the hash of the empty proof view. Caller construction
    of the cached digest remains in the initial environment relation. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_elements_input_hash_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_ptr_jets C.jet_uint32_array_init.
Require Import C.jet_elements_current_sequence_literal C.jet_elements_script_hash_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition haskell_amount_proof_view (a : amountWith (list byte)) : list byte :=
  match a with Explicit _ => [] | Confidential _ proof => proof end.

Definition haskell_issuance_proof_view (token : bool) (txi : sigTxInput) : list byte :=
  match sigTxiIssuance txi with
  | None => []
  | Some (inl new) => haskell_amount_proof_view
      (if token then newIssuanceTokenAmount new else newIssuanceAmount new)
  | Some (inr re) => if token then [] else haskell_amount_proof_view (reissuanceAmount re)
  end.

Lemma elements_issuance_asset_proof_view_matches txi :
  issuance_asset_proof_bytes txi = haskell_issuance_proof_view false txi.
Proof.
  unfold issuance_asset_proof_bytes, haskell_issuance_proof_view, haskell_amount_proof_view, viewPrf.
  destruct (sigTxiIssuance txi) as [[new|re]|]; reflexivity.
Qed.

Lemma elements_issuance_token_proof_view_matches txi :
  issuance_token_proof_bytes txi = haskell_issuance_proof_view true txi.
Proof.
  unfold issuance_token_proof_bytes, haskell_issuance_proof_view, haskell_amount_proof_view, viewPrf.
  destruct (sigTxiIssuance txi) as [[new|re]|]; reflexivity.
Qed.

Definition elements_issuance_asset_proof_literal_spec :=
  elements_input_digest_literal_spec (fun txi => byteStringHash (haskell_issuance_proof_view false txi)).

Definition elements_issuance_token_proof_literal_spec :=
  elements_input_digest_literal_spec (fun txi => byteStringHash (haskell_issuance_proof_view true txi)).

Lemma elements_issuance_asset_proof_literal_matches a environment :
  @elements_issuance_asset_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_issuance_asset_proof_literal_spec a environment.
Proof.
  rewrite elements_issuance_asset_proof_sem.
  unfold elements_issuance_asset_proof_result, elements_issuance_asset_proof_literal_spec.
  rewrite <- elements_input_digest_literal_matches.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|];
    [rewrite elements_issuance_asset_proof_view_matches|]; reflexivity.
Qed.

Lemma elements_issuance_token_proof_literal_matches a environment :
  @elements_issuance_token_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_issuance_token_proof_literal_spec a environment.
Proof.
  rewrite elements_issuance_token_proof_sem.
  unfold elements_issuance_token_proof_result, elements_issuance_token_proof_literal_spec.
  rewrite <- elements_input_digest_literal_matches.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|];
    [rewrite elements_issuance_token_proof_view_matches|]; reflexivity.
Qed.

Definition elements_current_issuance_asset_proof_literal_spec :=
  elements_current_literal_result elements_issuance_asset_proof_literal_spec.

Definition elements_current_issuance_token_proof_literal_spec :=
  elements_current_literal_result elements_issuance_token_proof_literal_spec.

Lemma elements_current_issuance_asset_proof_literal_matches a environment :
  @elements_current_issuance_asset_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_issuance_asset_proof_literal_spec a environment.
Proof.
  unfold elements_current_issuance_asset_proof_spec, elements_current_issuance_asset_proof_literal_spec.
  apply elements_current_literal_sem. exact elements_issuance_asset_proof_literal_matches.
Qed.

Lemma elements_current_issuance_token_proof_literal_matches a environment :
  @elements_current_issuance_token_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_issuance_token_proof_literal_spec a environment.
Proof.
  unfold elements_current_issuance_token_proof_spec, elements_current_issuance_token_proof_literal_spec.
  apply elements_current_literal_sem. exact elements_issuance_token_proof_literal_matches.
Qed.

Theorem elements_issuance_asset_proof_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset_proof elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => uint32_array_at m b ofs (issuance_asset_proof_words txi)) 544 360 0 696)
    elements_issuance_asset_proof_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_issuance_asset_proof_literal_matches|exact elements_issuance_asset_proof_local_spec].
Qed.

Theorem elements_issuance_token_proof_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token_proof elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => uint32_array_at m b ofs (issuance_token_proof_words txi)) 544 392 0 696)
    elements_issuance_token_proof_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_issuance_token_proof_literal_matches|exact elements_issuance_token_proof_local_spec].
Qed.

Theorem elements_current_issuance_asset_proof_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_issuance_asset_proof elements_ge Elements.env Ty.Unit Word256
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx
      (fun m b ofs txi => uint32_array_at m b ofs (issuance_asset_proof_words txi)) 544 360 0 696)
    elements_current_issuance_asset_proof_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_issuance_asset_proof_literal_matches|exact elements_current_issuance_asset_proof_local_spec].
Qed.

Theorem elements_current_issuance_token_proof_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_issuance_token_proof elements_ge Elements.env Ty.Unit Word256
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx
      (fun m b ofs txi => uint32_array_at m b ofs (issuance_token_proof_words txi)) 544 392 0 696)
    elements_current_issuance_token_proof_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_issuance_token_proof_literal_matches|exact elements_current_issuance_token_proof_local_spec].
Qed.

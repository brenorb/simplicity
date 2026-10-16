(** Original C issuance asset-amount getters against the literal optional
    issuance primitive. Reuse the Word64 confidential encoder and index/current
    routing; the original issuance tag, memory and framing relations remain. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_elements_output_nonce_literal C.jet_elements_amount_literal.
Require Import C.jet_elements_amount_jets.
Require Import C.jet_elements_sequence_literal.
Require Import C.jet_elements_issuance_amount_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_ptr_jets.
Require Import C.jet_elements_current_spec C.jet_elements_current_sequence_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Notation ConfAmount := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word64).

Definition issuance_asset_amount_literal (txi : sigTxInput) : tySem (Ty.Sum Ty.Unit ConfAmount) :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) => inr (encode_amount_literal (clearPrf (newIssuanceAmount new)))
  | Some (inr re) => inr (encode_amount_literal (clearPrf (reissuanceAmount re)))
  end.

Lemma issuance_asset_amount_literal_matches txi :
  (match sigTxiIssuance txi with
   | None => inl tt
   | Some i => inr (encode_amount (clearPrf (issuance_amount i)))
   end) = issuance_asset_amount_literal txi.
Proof.
  unfold issuance_asset_amount_literal.
  destruct (sigTxiIssuance txi) as [[new|re]|]; cbn [issuance_amount];
    [rewrite encode_amount_literal_matches|rewrite encode_amount_literal_matches|]; reflexivity.
Qed.

Definition elements_issuance_asset_amount_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  @word_indexed_value_literal sigTxInput (Ty.Sum Ty.Unit ConfAmount) 5
    issuance_asset_amount_literal (sigTxIn (Elements.envTx environment)) a.

Lemma elements_issuance_asset_amount_literal_matches a environment :
  @elements_issuance_asset_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_issuance_asset_amount_literal_spec a environment.
Proof.
  rewrite elements_issuance_asset_amount_sem.
  unfold issuance_amount_result, elements_issuance_asset_amount_literal_spec.
  apply (@word_indexed_value_literal_matches sigTxInput (Ty.Sum Ty.Unit ConfAmount) 5
    (fun txi => match sigTxiIssuance txi with
                | None => inl tt
                | Some i => inr (encode_amount (clearPrf (issuance_amount i)))
                end)
    issuance_asset_amount_literal (sigTxIn (Elements.envTx environment)) a).
  exact issuance_asset_amount_literal_matches.
Qed.

Definition elements_current_issuance_asset_amount_literal_spec :=
  elements_current_literal_result elements_issuance_asset_amount_literal_spec.

Lemma elements_current_issuance_asset_amount_literal_matches a environment :
  @elements_current_issuance_asset_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_issuance_asset_amount_literal_spec a environment.
Proof.
  unfold elements_current_issuance_asset_amount_spec, elements_current_issuance_asset_amount_literal_spec.
  apply (elements_current_literal_sem (B := Ty.Sum Ty.Unit ConfAmount)).
  exact elements_issuance_asset_amount_literal_matches.
Qed.

Theorem elements_issuance_asset_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfAmount))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_amount_rep 544 256 0 696)
    elements_issuance_asset_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_issuance_asset_amount_literal_matches|exact elements_issuance_asset_amount_local_spec].
Qed.

Theorem elements_current_issuance_asset_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_issuance_asset_amount elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit ConfAmount)
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx issuance_amount_rep 544 256 0 696)
    elements_current_issuance_asset_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_issuance_asset_amount_literal_matches|exact elements_current_issuance_asset_amount_local_spec].
Qed.

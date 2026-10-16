(** Whole original C token-amount jets against literal optional issuance values:
    new token amount, explicit zero for reissuance, or absent issuance. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_elements_amount_jets C.jet_elements_sequence_literal.
Require Import C.jet_elements_output_nonce_literal C.jet_elements_amount_literal.
Require Import C.jet_elements_token_select C.jet_elements_token_amount_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_ptr_jets.
Require Import C.jet_elements_current_spec C.jet_elements_current_sequence_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Notation ConfAmount := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word64).

Definition issuance_token_amount_literal (txi : sigTxInput) : tySem (Ty.Sum Ty.Unit ConfAmount) :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) => inr (encode_amount_literal (clearPrf (newIssuanceTokenAmount new)))
  | Some (inr _) => inr (encode_amount_literal (Explicit Int64.zero))
  end.

Lemma issuance_token_amount_literal_matches txi : issuance_token_value txi = issuance_token_amount_literal txi.
Proof.
  unfold issuance_token_value, issuance_token_amount_literal.
  destruct (sigTxiIssuance txi) as [[new|re]|]; cbn [token_selected_amount];
    [rewrite encode_amount_literal_matches|rewrite encode_amount_literal_matches|]; reflexivity.
Qed.

Definition elements_issuance_token_amount_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  @word_indexed_value_literal sigTxInput (Ty.Sum Ty.Unit ConfAmount) 5
    issuance_token_amount_literal (sigTxIn (Elements.envTx environment)) a.

Lemma elements_issuance_token_amount_literal_matches a environment :
  @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_issuance_token_amount_literal_spec a environment.
Proof.
  rewrite elements_issuance_token_amount_sem.
  unfold issuance_token_result, elements_issuance_token_amount_literal_spec.
  apply (@word_indexed_value_literal_matches sigTxInput (Ty.Sum Ty.Unit ConfAmount) 5
    issuance_token_value issuance_token_amount_literal (sigTxIn (Elements.envTx environment)) a).
  exact issuance_token_amount_literal_matches.
Qed.

Definition elements_current_issuance_token_amount_literal_spec :=
  elements_current_literal_result elements_issuance_token_amount_literal_spec.

Lemma elements_current_issuance_token_amount_literal_matches a environment :
  @elements_current_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_issuance_token_amount_literal_spec a environment.
Proof.
  unfold elements_current_issuance_token_amount_spec, elements_current_issuance_token_amount_literal_spec.
  apply (elements_current_literal_sem (B := Ty.Sum Ty.Unit ConfAmount)).
  exact elements_issuance_token_amount_literal_matches.
Qed.

Theorem elements_issuance_token_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfAmount))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_token_rep 544 256 0 696)
    elements_issuance_token_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_issuance_token_amount_literal_matches|exact elements_issuance_token_amount_local_spec].
Qed.

Theorem elements_current_issuance_token_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_issuance_token_amount elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit ConfAmount)
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx issuance_token_rep 544 256 0 696)
    elements_current_issuance_token_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_issuance_token_amount_literal_matches|exact elements_current_issuance_token_amount_local_spec].
Qed.

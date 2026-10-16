(** C amount jets against the canonical amount/asset pair programs. Reuse the
    payload-polymorphic confidential encoder; explicit amounts are Word64. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_haskell_word_conversion C.jet_elements_sequence_literal.
Require Import C.jet_elements_output_nonce_literal C.jet_elements_asset_literal C.jet_elements_asset_jets.
Require Import C.jet_elements_amount_jets C.jet_elements_current_gen C.jet_elements_current_gen_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_spec C.jet_elements_current_sequence_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Notation ConfLiteral a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).
Local Notation AmountPair := (Ty.Prod (ConfLiteral Word256) (ConfLiteral Word64)).

Definition encode_amount_literal (a : amountWith unit) : tySem (ConfLiteral Word64) :=
  encode_confidential_literal (fun v => haskell_to_word 6 (Int64.unsigned v)) a.

Lemma encode_amount_literal_matches a : encode_amount a = encode_amount_literal a.
Proof.
  unfold encode_amount, encode_amount_literal, conf_toBit.
  apply (@encode_confidential_literal_matches int64 Word64
    (fun v => @fromZ (WordToZ 6) (Int64.unsigned v))
    (fun v => haskell_to_word 6 (Int64.unsigned v)) a).
  intro v. symmetry. apply haskell_to_word_matches.
Qed.

Definition amount_pair_literal {X : Type} (values : list X)
    (asset_of : X -> assetWith unit) (amount_of : X -> amountWith unit)
    (a : tySem Word32) : option (tySem (Ty.Sum Ty.Unit AmountPair)) :=
  @word_indexed_value_literal X AmountPair 5
    (fun x => (encode_asset_literal (asset_of x), encode_amount_literal (amount_of x))) values a.

Lemma amount_pair_literal_matches {X : Type} (values : list X) asset_of amount_of a :
  Some (amount_pair_result values asset_of amount_of a) =
    amount_pair_literal values asset_of amount_of a.
Proof.
  unfold amount_pair_result, amount_pair_literal.
  apply (@word_indexed_value_literal_matches X AmountPair 5
    (fun x => (encode_asset (asset_of x), encode_amount (amount_of x)))
    (fun x => (encode_asset_literal (asset_of x), encode_amount_literal (amount_of x))) values a).
  intro x. rewrite encode_asset_literal_matches, encode_amount_literal_matches. reflexivity.
Qed.

Definition elements_input_amount_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  amount_pair_literal (sigTxIn (Elements.envTx environment))
    (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) a.

Lemma elements_input_amount_literal_matches a environment :
  @elements_input_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_amount_literal_spec a environment.
Proof.
  rewrite elements_input_amount_sem. unfold elements_input_amount_literal_spec.
  apply amount_pair_literal_matches.
Qed.

Definition elements_output_amount_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  amount_pair_literal (sigTxOut (Elements.envTx environment))
    (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) a.

Lemma elements_output_amount_literal_matches a environment :
  @elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_amount_literal_spec a environment.
Proof.
  rewrite elements_output_amount_sem. unfold elements_output_amount_literal_spec.
  apply amount_pair_literal_matches.
Qed.

Definition elements_current_amount_literal_spec :=
  elements_current_literal_result elements_input_amount_literal_spec.

Lemma elements_current_amount_literal_matches a environment :
  @elements_current_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_amount_literal_spec a environment.
Proof.
  unfold elements_current_amount_spec, elements_current_amount_literal_spec.
  apply (elements_current_literal_sem (B := AmountPair)).
  exact elements_input_amount_literal_matches.
Qed.

Theorem elements_input_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit AmountPair)
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b (ofs + 168) (utxoAsset (sigTxiTxo txi)) /\
        amount_rep m b (ofs + 208) (utxoAmount (sigTxiTxo txi))) 544 0 0 696)
    elements_input_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_amount_literal_matches|exact elements_input_amount_local_spec].
Qed.

Theorem elements_output_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit AmountPair)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => asset_rep m b (ofs + 0) (clearPrf (txoAsset txo)) /\
        amount_rep m b (ofs + 104) (clearPrf (txoAmount txo))) 248 0 8 704)
    elements_output_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_output_amount_literal_matches|exact elements_output_amount_local_spec].
Qed.

Theorem elements_current_amount_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_amount elements_ge Elements.env Ty.Unit
    AmountPair
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) input_amount_elem_rep 544 0 696)
    elements_current_amount_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_amount_literal_matches|exact elements_current_amount_local_spec].
Qed.

(** Original C asset getters against literal primitive encoding. A point's
    hash256 field represents the serialized fe_pack word. This is a projection
    interface, not a claim that every arbitrary word is a canonical FE. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word C.jet_elements_sequence_literal.
Require Import C.jet_elements_output_nonce_literal C.jet_elements_asset_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_current_ptr_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_current_spec C.jet_elements_current_sequence_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Notation ConfLiteral a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).
Local Notation AssetConf := (ConfLiteral Word256).

(** Haskell fe_repr = toInteger . fe_pack. The packed word is read in the
    existing four-limb serialization order; no field reduction is performed. *)
Definition packed_fe_integer_literal (packed : hash256) : Z :=
  haskell_word256_integer
    (haskell_be256_run (hash256_to_bytelist packed) (haskell_word256_from_integer 0)).

Lemma packed_fe_to_word_literal_matches packed :
  haskell_to_word 8 (packed_fe_integer_literal packed) = from_hash256 packed.
Proof. apply native_hash_word_literal_matches. Qed.

Definition encode_confidential_literal {A : Set} {B : Ty}
    (enc : A -> tySem B) (c : confidential unit A) : tySem (ConfLiteral B) :=
  match c with
  | Explicit x => inr (enc x)
  | Confidential (Point odd packed) _ =>
      inl ((if odd then inr tt else inl tt), haskell_to_word 8 (packed_fe_integer_literal packed))
  end.

Lemma encode_confidential_literal_matches {A : Set} {B : Ty}
    (old literal : A -> tySem B) (c : confidential unit A) :
  (forall x, old x = literal x) ->
  (match c with
   | Explicit x => inr (old x)
   | Confidential (Point odd packed) _ =>
       inl ((if odd then inr tt else inl tt), from_hash256 packed)
   end : tySem (ConfLiteral B)) = encode_confidential_literal literal c.
Proof.
  intro Henc. destruct c as [x|[odd packed] proof]; cbn [encode_confidential_literal].
  - rewrite Henc. reflexivity.
  - rewrite packed_fe_to_word_literal_matches. reflexivity.
Qed.

Definition encode_asset_literal (a : assetWith unit) : tySem AssetConf :=
  encode_confidential_literal
    (fun h => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) a.

Lemma encode_asset_literal_matches a : encode_asset a = encode_asset_literal a.
Proof.
  unfold encode_asset, encode_asset_literal, conf_toBit.
  apply (@encode_confidential_literal_matches hash256 Word256 from_hash256
    (fun h => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) a).
  intro h. symmetry. apply haskell_hash_word256.
Qed.

Definition elements_input_asset_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  word_indexed_value_literal 5 (fun txi => encode_asset_literal (utxoAsset (sigTxiTxo txi)))
    (sigTxIn (Elements.envTx environment)) a.

Lemma elements_input_asset_literal_matches a environment :
  @elements_input_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_asset_literal_spec a environment.
Proof.
  rewrite elements_input_asset_sem.
  unfold elements_input_asset_result, elements_input_asset_literal_spec.
  apply (@word_indexed_value_literal_matches sigTxInput AssetConf 5
    (fun txi => encode_asset (utxoAsset (sigTxiTxo txi)))
    (fun txi => encode_asset_literal (utxoAsset (sigTxiTxo txi)))
    (sigTxIn (Elements.envTx environment)) a).
  intro txi. apply encode_asset_literal_matches.
Qed.

Definition elements_output_asset_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  word_indexed_value_literal 5 (fun txo => encode_asset_literal (clearPrf (txoAsset txo)))
    (sigTxOut (Elements.envTx environment)) a.

Lemma elements_output_asset_literal_matches a environment :
  @elements_output_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_asset_literal_spec a environment.
Proof.
  rewrite elements_output_asset_sem.
  unfold elements_output_asset_result, elements_output_asset_literal_spec.
  apply (@word_indexed_value_literal_matches txOutput AssetConf 5
    (fun txo => encode_asset (clearPrf (txoAsset txo)))
    (fun txo => encode_asset_literal (clearPrf (txoAsset txo)))
    (sigTxOut (Elements.envTx environment)) a).
  intro txo. apply encode_asset_literal_matches.
Qed.

Definition elements_current_asset_literal_spec :=
  elements_current_literal_result elements_input_asset_literal_spec.

Lemma elements_current_asset_literal_matches a environment :
  @elements_current_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_asset_literal_spec a environment.
Proof.
  unfold elements_current_asset_spec, elements_current_asset_literal_spec.
  apply (elements_current_literal_sem (B := AssetConf)).
  exact elements_input_asset_literal_matches.
Qed.

Theorem elements_input_asset_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_asset elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit AssetConf)
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))) 544 168 0 696)
    elements_input_asset_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_asset_literal_matches|exact elements_input_asset_local_spec].
Qed.

Theorem elements_output_asset_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_asset elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit AssetConf)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => asset_rep m b ofs (clearPrf (txoAsset txo))) 248 0 8 704)
    elements_output_asset_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_output_asset_literal_matches|exact elements_output_asset_local_spec].
Qed.

Theorem elements_current_asset_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_asset elements_ge Elements.env Ty.Unit
    AssetConf
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx
      (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))) 544 168 0 696)
    elements_current_asset_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_asset_literal_matches|exact elements_current_asset_local_spec].
Qed.

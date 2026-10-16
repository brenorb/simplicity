(** Original C output_nonce against the literal indexed optional-nonce
    primitive. Native Word256 nonce payloads are not field elements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_haskell_word_conversion C.jet_elements_sequence_literal C.jet_haskell_hash_word.
Require Import C.jet_elements_tap_getters_literal C.jet_elements_asset_jets C.jet_elements_indexed_ptr.
Require Import C.jet_word_repr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Notation ConfNonce := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word256).

(** Decode the four serialized native Word64 limbs, then toInteger/toWord256.
    The same bridge applies to raw nonce words and raw Schnorr public keys. *)
Definition native_hash_word_literal (h : hash256) : tySem Word256 :=
  haskell_to_word 8 (haskell_word256_integer
    (haskell_be256_run (hash256_to_bytelist h) (haskell_word256_from_integer 0))).

Lemma native_hash_word_literal_matches h : native_hash_word_literal h = from_hash256 h.
Proof. apply haskell_hash_word256. Qed.

Definition nonce_payload_literal (n : nonce) : tySem ConfNonce :=
  match n with
  | inl (odd, w) => inl ((if odd then inr tt else inl tt), native_hash_word_literal w)
  | inr h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  end.

Definition encode_nonce_literal (n : option nonce) : tySem (Ty.Sum Ty.Unit ConfNonce) :=
  match n with None => inl tt | Some v => inr (nonce_payload_literal v) end.

Lemma encode_nonce_literal_matches n : encode_nonce n = encode_nonce_literal n.
Proof.
  destruct n as [[[odd w]|h]|]; unfold encode_nonce, encode_nonce_literal, nonce_payload_literal;
    cbn [encode_asset nonce_conf];
    [rewrite native_hash_word_literal_matches; reflexivity|
     rewrite haskell_hash_word256; reflexivity|reflexivity].
Qed.

(** Share the index/fromWord/listToMaybe/drop routing independently of the
    payload's sum shape, so future indexed getters need only an encoder bridge. *)
Definition word_indexed_value_literal {A : Type} {B : Ty} (depth : nat)
    (enc : A -> tySem B) (values : list A) (a : tySem (Word depth)) :
    option (tySem (Ty.Sum Ty.Unit B)) :=
  Some (match hd_error (skipn (Z.to_nat (haskell_from_word depth a)) values) with
        | None => inl tt | Some v => inr (enc v) end).

Lemma word_indexed_value_literal_matches {A : Type} {B : Ty} depth
    (enc literal : A -> tySem B) values a :
  (forall x, enc x = literal x) ->
  Some (match nth_error values (Z.to_nat (@toZ (WordToZ depth) a)) with
        | None => inl tt | Some v => inr (enc v) end) =
    word_indexed_value_literal depth literal values a.
Proof.
  intro Henc. unfold word_indexed_value_literal.
  rewrite haskell_from_word_matches, <- nth_error_is_list_to_maybe_drop.
  destruct (nth_error values (Z.to_nat (@toZ (WordToZ depth) a))) as [v|];
    [rewrite Henc|]; reflexivity.
Qed.

Lemma output_nonce_literal_index_range (a : tySem Word32) :
  0 <= haskell_from_word 5 a < 4294967296.
Proof. rewrite haskell_from_word_matches. exact (word_toZ_range 5 a). Qed.

Definition elements_output_nonce_literal_spec (a : tySem Word32) (environment : Elements.env) :=
  word_indexed_value_literal 5 (fun txo => encode_nonce_literal (txoNonce txo))
    (sigTxOut (Elements.envTx environment)) a.

Lemma elements_output_nonce_literal_matches a environment :
  @elements_output_nonce_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_nonce_literal_spec a environment.
Proof.
  rewrite elements_output_nonce_sem.
  unfold elements_output_nonce_result, elements_output_nonce_literal_spec.
  apply (word_indexed_value_literal_matches (A := txOutput)
    (B := Ty.Sum Ty.Unit ConfNonce) 5
    (fun txo => encode_nonce (txoNonce txo))
    (fun txo => encode_nonce_literal (txoNonce txo))
    (sigTxOut (Elements.envTx environment)) a).
  intro txo. apply encode_nonce_literal_matches.
Qed.

Theorem elements_output_nonce_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_nonce elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfNonce))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => nonce_rep m b ofs (txoNonce txo)) 248 144 8 704)
    elements_output_nonce_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_output_nonce_literal_matches|exact elements_output_nonce_local_spec].
Qed.

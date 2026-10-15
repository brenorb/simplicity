(** Actual C internal-key and tappath contracts. The key is a raw four-limb
    Word256, not a curve point; path hashing uses the same checked decoder.
    The indexing helper is polymorphic in logical word depth; only the byte
    instance is claimed here as a Haskell drop-index correspondence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_haskell_word_conversion C.jet_elements_sequence_literal C.jet_haskell_hash_word.
Require Import C.jet_elements_hash_field_jets C.jet_elements_hash_getter_local.
Require Import C.jet_elements_tappath_local C.jet_elements_tappath_nullable.
Require Import C.jet_word_repr.
Set Default Timeout 10.
Local Open Scope Z_scope.

Definition haskell_encode_pubkey (h : hash256) : tySem Word256 :=
  haskell_to_word 8 (haskell_word256_integer
    (haskell_be256_run (hash256_to_bytelist h) (haskell_word256_from_integer 0))).

Lemma haskell_encode_pubkey_matches h : haskell_encode_pubkey h = from_hash256 h.
Proof. apply haskell_hash_word256. Qed.

Definition elements_internal_key_literal_spec (_ : tySem Ty.Unit) (environment : Elements.env) :=
  Some (haskell_encode_pubkey (tapInternalKey (Elements.envTap environment))).

Lemma elements_internal_key_literal_matches a environment :
  @elements_internal_key_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_internal_key_literal_spec a environment.
Proof.
  destruct a. change (Some (from_hash256 (tapInternalKey (Elements.envTap environment))) =
    elements_internal_key_literal_spec tt environment).
  unfold elements_internal_key_literal_spec. f_equal. symmetry. apply haskell_encode_pubkey_matches.
Qed.

Lemma nth_error_is_list_to_maybe_drop {A : Type} (xs : list A) n :
  nth_error xs n = hd_error (skipn n xs).
Proof. revert xs. induction n as [|n IH]; intros [|x xs]; cbn; try reflexivity; apply IH. Qed.

Definition word_indexed_digest_literal (depth : nat) (values : list hash256)
    (a : tySem (Word depth)) : option (tySem (Ty.Sum Ty.Unit Word256)) :=
  Some (match hd_error (skipn (Z.to_nat (haskell_from_word depth a)) values) with
        | None => inl tt
        | Some h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) end).

Lemma word_indexed_digest_literal_matches depth values a :
  Some (match nth_error values (Z.to_nat (@toZ (WordToZ depth) a)) with
        | None => inl tt | Some h => inr (from_hash256 h) end) =
    word_indexed_digest_literal depth values a.
Proof.
  unfold word_indexed_digest_literal. rewrite haskell_from_word_matches, <- nth_error_is_list_to_maybe_drop.
  destruct (nth_error values (Z.to_nat (@toZ (WordToZ depth) a))) as [h|];
    [rewrite haskell_hash_word256|]; reflexivity.
Qed.

Lemma tappath_literal_index_range (a : tySem Word8) :
  0 <= haskell_from_word 3 a < 256.
Proof. rewrite haskell_from_word_matches. exact (word_toZ_range 3 a). Qed.

Definition elements_tappath_literal_spec (a : tySem Word8) (environment : Elements.env) :=
  word_indexed_digest_literal 3 (tappath (Elements.envTap environment)) a.

Lemma elements_tappath_literal_matches a environment :
  @elements_tappath_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_tappath_literal_spec a environment.
Proof.
  rewrite elements_tappath_sem. unfold elements_tappath_result, elements_tappath_literal_spec.
  apply word_indexed_digest_literal_matches.
Qed.

Theorem elements_internal_key_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_internal_key elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => tapInternalKey (Elements.envTap e)) 8 104 176)
    elements_internal_key_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_internal_key_literal_matches|exact elements_internal_key_local_spec].
Qed.

Theorem elements_tappath_nullable_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tappath elements_ge Elements.env Word8
    (Ty.Sum Ty.Unit Word256) elements_tappath_env_rep_nullable elements_tappath_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_tappath_literal_matches|exact elements_tappath_nullable_local_spec].
Qed.

Theorem elements_tappath_u8_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tappath elements_ge Elements.env Word8
    (Ty.Sum Ty.Unit Word256) elements_tappath_env_rep_u8 elements_tappath_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_tappath_literal_matches|exact elements_tappath_u8_local_spec].
Qed.

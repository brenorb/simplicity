(** Canonical Bitcoin outpoint/annex context programs. Their option bridges
    retain every context, counter and optional-input case. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_haskell_word_conversion.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_bitcoin_outpoint_hash {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type :=
  (O H &&& I O H >>> @literal_ctx8_addn 5 term) &&& I I H >>> @literal_ctx8_addn 2 term.

Lemma literal_bitcoin_outpoint_hash_matches :
  @literal_bitcoin_outpoint_hash optalg = @outpoint_hash_spec optalg.
Proof.
  unfold literal_bitcoin_outpoint_hash, outpoint_hash_spec.
  rewrite (literal_ctx8_addn_matches 5), (literal_ctx8_addn_matches 2). reflexivity.
Qed.

Definition literal_bitcoin_annex_hash {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type :=
  I H &&& O H >>> case
    (I H &&& O (@Word.zero 3 (Alg.Assertion.toCore term)) >>> @literal_ctx8_add1 term)
    ((I H &&& (unit >>> Alg.scribe (haskell_to_word 3 0x01)) >>> @literal_ctx8_add1 term)
      &&& O H >>> @literal_ctx8_addn 5 term).

Lemma literal_bitcoin_annex_hash_matches :
  @literal_bitcoin_annex_hash optalg = @annex_hash_spec optalg.
Proof.
  unfold literal_bitcoin_annex_hash, annex_hash_spec, byte_one.
  rewrite haskell_to_word_matches, literal_ctx8_add1_matches, literal_ctx8_addn_matches.
  reflexivity.
Qed.

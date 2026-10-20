(** Canonical SHA array-hashing programs in any assertion algebra, including
    primitive-bearing algebras. These equalities are consumed by C jet proofs;
    no claim of additional C coverage follows from this module alone. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sha256_ctx8_init_spec C.jet_forWhile_spec.
Require Import C.jet_sha256_iv_init C.jet_buffer_empty_spec C.jet_haskell_word_conversion.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal.
Require Import C.jet_sha_hash_loop C.jet_sha_hash_words.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_sha_hash_ctx_init {term : Alg.Core.Algebra} : term Ty.Unit sha256_ctx8_type :=
  @buffer_empty_spec (Word 3) 5 Ty.Unit term &&&
    (@Word.zero 6 term &&& Alg.scribe (haskell_to_word 8
      0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19)).

Lemma literal_sha_hash_ctx_init_matches term :
  @literal_sha_hash_ctx_init term = @sha256_ctx8_init_spec term.
Proof.
  unfold literal_sha_hash_ctx_init, sha256_ctx8_init_spec, sha256_iv_spec.
  rewrite haskell_to_word_matches. reflexivity.
Qed.

Definition literal_sha_hash_loop_body k {term : Alg.Assertion.Algebra} {C W : Ty}
    (array : term (Ty.Prod C W) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :
    term (Ty.Prod (Ty.Prod C W) sha256_ctx8_type) (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  O array &&& I H >>> case (injl (I H)) (injr (I H &&& O H >>> @literal_ctx8_addn k term)).

Lemma literal_sha_hash_loop_body_matches k term C W array :
  @literal_sha_hash_loop_body k term C W array = @hash_loop_body k term C W array.
Proof.
  unfold literal_sha_hash_loop_body, hash_loop_body.
  rewrite literal_ctx8_addn_algebra_matches. reflexivity.
Qed.

Definition literal_sha_hash_loop k w {term : Alg.Assertion.Algebra} {C : Ty}
    (array : term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :
    term (Ty.Prod C sha256_ctx8_type) sha256_ctx8_type :=
  @for_while_program w C sha256_ctx8_type sha256_ctx8_type (Alg.Assertion.toCore term)
    (@literal_sha_hash_loop_body k term C (Word w) array) >>> copair iden iden.

Lemma literal_sha_hash_loop_matches k w term C array :
  @literal_sha_hash_loop k w term C array = @hash_loop_spec k w term C array.
Proof.
  unfold literal_sha_hash_loop, hash_loop_spec.
  rewrite literal_sha_hash_loop_body_matches. reflexivity.
Qed.

Definition literal_sha_hash_words k w {term : Alg.Assertion.Algebra} {C : Ty}
    (array : term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k))) : term C Word256 :=
  iden &&& (unit >>> @literal_sha_hash_ctx_init (Alg.Assertion.toCore term)) >>>
    @literal_sha_hash_loop k w term C array >>> @literal_ctx8_finalize term.

Lemma literal_sha_hash_words_matches k w term C array :
  @literal_sha_hash_words k w term C array = @hash_words_spec k w term C array.
Proof.
  unfold literal_sha_hash_words, hash_words_spec.
  rewrite literal_sha_hash_ctx_init_matches, literal_sha_hash_loop_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

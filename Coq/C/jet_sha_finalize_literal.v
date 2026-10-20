(** Canonical finalizer tree: count assertion/clearing, padding, bit length
    and the final block call. Reuse the verified C-to-SHA proof downstream. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_buffer_empty_spec C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_spec C.jet_sha256_count_assertion.
Require Import C.jet_core_pad_spec C.jet_sha_finalize_literal_word C.jet_sha_block_literal.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_sha_pad01 {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 0) (Word 4) :=
  copair (@Word.zero 4 term) (iden &&& (unit >>> @Word.zero 3 term)).
Definition literal_sha_pad03 {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 1) (Word 5) :=
  O H &&& I (@literal_sha_pad01 term) >>> case (I H &&& O (@Word.zero 4 term)) iden.
Definition literal_sha_pad07 {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 2) (Word 6) :=
  O H &&& I (@literal_sha_pad03 term) >>> case (I H &&& O (@Word.zero 5 term)) iden.
Definition literal_sha_pad015 {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 3) (Word 7) :=
  O H &&& I (@literal_sha_pad07 term) >>> case (I H &&& O (@Word.zero 6 term)) iden.
Definition literal_sha_pad031 {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 4) (Word 8) :=
  O H &&& I (@literal_sha_pad015 term) >>> case (I H &&& O (@Word.zero 7 term)) iden.
Definition literal_sha_pad063 {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 5) (Word 9) :=
  O H &&& I (@literal_sha_pad031 term) >>> case (I H &&& O (@Word.zero 8 term)) iden.

Lemma literal_sha_pad063_matches term :
  @literal_sha_pad063 term = @buffer_pad_spec 5 term.
Proof. reflexivity. Qed.

Definition literal_sha_buffer63_size {term : Alg.Core.Algebra} :
    term (buffer_type (Word 3) 5) (Word 3) :=
  ((Bit.false &&& Bit.false) &&& (O (copair Bit.false Bit.true) &&& I (O (copair Bit.false Bit.true))))
    &&& I (I ((O (copair Bit.false Bit.true) &&& I (O (copair Bit.false Bit.true)))
      &&& I (I (O (copair Bit.false Bit.true) &&& I (copair Bit.false Bit.true))))).

Lemma literal_sha_buffer63_size_matches term :
  @literal_sha_buffer63_size term = @buffer63_size_spec term.
Proof. reflexivity. Qed.

Definition literal_ctx8_bitlen {term : Alg.Core.Algebra} : term sha256_ctx8_type (Word 6) :=
  (O (@literal_sha_buffer63_size term) >>> @left_pad_low_spec term 3 3)
    &&& I (O (@literal_sha_left_shift64 6 term)) >>>
    @literal_sha_add64 term >>> @literal_sha_left_shift64 3 term.

Lemma literal_ctx8_bitlen_matches term : @literal_ctx8_bitlen term = @ctx8_bitlen_spec term.
Proof.
  unfold literal_ctx8_bitlen.
  rewrite literal_sha_buffer63_size_matches, literal_sha_add64_matches.
  rewrite !literal_sha_left_shift64_matches by (cbn; tauto).
  reflexivity.
Qed.

Definition literal_ctx8_clear_count {term : Alg.Assertion.Algebra} : term sha256_ctx8_type sha256_ctx8_type :=
  O H &&& ((@literal_ctx8_verify_count term >>> @Word.zero 6 (Alg.Assertion.toCore term)) &&& I I H).

Lemma literal_ctx8_clear_count_matches term : @literal_ctx8_clear_count term = @ctx8_clear_count_spec term.
Proof. unfold literal_ctx8_clear_count. rewrite literal_ctx8_verify_count_matches. reflexivity. Qed.

Lemma literal_sha_pad_word64_matches : pad_word64 = @fromZ (WordToZ 6) (2^63)%Z.
Proof. reflexivity. Qed.

Definition literal_ctx8_finalize_pad {term : Alg.Assertion.Algebra} :
    term sha256_ctx8_type (Ty.Prod (Word 9) (Word 8)) :=
  (@literal_ctx8_clear_count term &&& (unit >>> Alg.scribe pad_word64)) >>>
    @literal_ctx8_addn 3 term >>> (O (@literal_sha_pad063 (Alg.Assertion.toCore term)) &&& I I H).

Lemma literal_ctx8_finalize_pad_algebra_matches term :
  @literal_ctx8_finalize_pad term = @ctx8_finalize_pad_spec term.
Proof.
  unfold literal_ctx8_finalize_pad.
  rewrite literal_ctx8_clear_count_matches, literal_ctx8_addn_algebra_matches, literal_sha_pad063_matches.
  unfold ctx8_finalize_pad_spec. reflexivity.
Qed.

Lemma literal_ctx8_finalize_pad_matches :
  @literal_ctx8_finalize_pad optalg = @ctx8_finalize_pad_spec optalg.
Proof.
  unfold literal_ctx8_finalize_pad.
  rewrite literal_ctx8_clear_count_matches, literal_ctx8_addn_matches, literal_sha_pad063_matches.
  unfold ctx8_finalize_pad_spec.
  reflexivity.
Qed.

Definition literal_ctx8_finalize_block {term : Alg.Core.Algebra} :
    term (Ty.Prod (Ty.Prod (Word 9) (Word 8)) (Word 6)) (Ty.Prod (Word 8) (Word 9)) :=
  O I H &&& (O O O H &&& (O (O I O H) &&& (O (O (I I O H)) &&& I H))).

Lemma literal_ctx8_finalize_block_matches term :
  @literal_ctx8_finalize_block term = @ctx8_finalize_block_spec term.
Proof. reflexivity. Qed.

Definition literal_ctx8_finalize {term : Alg.Assertion.Algebra} : term sha256_ctx8_type (Word 8) :=
  @literal_ctx8_finalize_pad term &&& @literal_ctx8_bitlen (Alg.Assertion.toCore term) >>>
    @literal_ctx8_finalize_block (Alg.Assertion.toCore term) >>> @literal_sha_256_block (Alg.Assertion.toCore term).

Lemma literal_ctx8_finalize_algebra_matches term : @literal_ctx8_finalize term = @ctx8_finalize_spec term.
Proof.
  unfold literal_ctx8_finalize.
  rewrite literal_ctx8_finalize_pad_algebra_matches, literal_ctx8_bitlen_matches,
    literal_ctx8_finalize_block_matches, literal_sha_256_block_core_matches.
  unfold ctx8_finalize_spec. reflexivity.
Qed.

Lemma literal_ctx8_finalize_matches : @literal_ctx8_finalize optalg = @ctx8_finalize_spec optalg.
Proof.
  unfold literal_ctx8_finalize.
  rewrite literal_ctx8_finalize_pad_matches, literal_ctx8_bitlen_matches,
    literal_ctx8_finalize_block_matches, literal_sha_block_option_matches.
  unfold ctx8_finalize_spec.
  reflexivity.
Qed.

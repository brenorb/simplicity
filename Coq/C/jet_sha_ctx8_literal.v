(** Literal context-add program with the canonical SHA block boundary.
    Reuse the existing buffer/counter/increment ports, whose source
    correspondence is checked separately; do not replace the program by
    a numerical byte-list model. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_sha_ctx8_spec C.jet_sha_block_literal.
Require Import C.jet_canonical_add_adapter.
Require Import C.jet_buffer_empty_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_increment_spec C.jet_assertion_spec C.jet_sha256_count_assertion.
Require Import C.jet_order_spec.
Local Open Scope term_scope.
Set Default Timeout 10.

Lemma literal_sha_add32_parametric : Alg.Core.Parametric (@literal_sha_add32).
Proof.
  intros alg1 alg2 R. unfold literal_sha_add32.
  apply Alg.comp_Parametric; [apply canonical_add_word_parametric|].
  apply Alg.drop_Parametric, Alg.iden_Parametric.
Qed.

Lemma literal_sha_add32_option_matches :
  @literal_sha_add32 (Alg.Assertion.toCore optalg) =
  @Simplicity.SHA256.add32 (Alg.Assertion.toCore optalg).
Proof. apply literal_sha_add32_core_matches. Qed.

Lemma literal_sha_block_option_matches :
  @literal_sha_256_block (Alg.Assertion.toCore optalg) =
  @Simplicity.SHA256.hashBlock (Alg.Assertion.toCore optalg).
Proof. apply literal_sha_256_block_core_matches. Qed.

Definition literal_ctx8_no_carry {term : Alg.Assertion.Algebra} :
    term (Ty.Prod Bit (Word 6)) (Word 6) :=
  @Alg.Assertion.Combinators.assertl Ty.Unit Ty.Unit (Word 6) (Word 6) term
    (I H) assertion_cmr_fail0.

Definition literal_ctx8_increment64 {term : Alg.Core.Algebra} :
    term (Word 6) (Ty.Prod Bit (Word 6)) :=
  Bit.true &&& H >>>
    (O H &&& (I H &&& (unit >>> @Word.zero 6 term)) >>> @Word.fullAdder 6 term).

Lemma literal_ctx8_increment64_matches term :
  @literal_ctx8_increment64 term = @increment_word_spec term 6.
Proof. reflexivity. Qed.

Definition literal_ctx8_snoc {term : Alg.Core.Algebra} :
    term (Ty.Prod sha256_ctx8_type (Word 3)) (Ty.Prod (Ty.Sum (Word 9) ctx8_buf) ctx8_tail) :=
  (O O H &&& I H >>> @buffer_snoc_spec (Word 3) 5 term) &&& O I H.

Definition literal_ctx8_count_check {term : Alg.Core.Algebra} : term sha256_ctx8_type Bit :=
  (I O H &&& (unit >>> Alg.scribe sha256_count_limit)) >>> @lt_word_spec term 6.

Definition literal_ctx8_verify_count {term : Alg.Assertion.Algebra} : term sha256_ctx8_type Ty.Unit :=
  (@literal_ctx8_count_check (Alg.Assertion.toCore term) &&& unit) >>>
    @Alg.Assertion.Combinators.assertr Ty.Unit Ty.Unit Ty.Unit Ty.Unit term assertion_cmr_fail0 (O H).

Lemma literal_ctx8_snoc_matches term : @literal_ctx8_snoc term = @ctx8_add1_snoc term.
Proof. reflexivity. Qed.

Lemma literal_ctx8_verify_count_matches term :
  @literal_ctx8_verify_count term = @sha256_count_assertion_spec term.
Proof. reflexivity. Qed.

Lemma literal_ctx8_count_limit_matches :
  sha256_count_limit = @fromZ (WordToZ 6) (2^55)%Z.
Proof. reflexivity. Qed.

Definition literal_ctx8_add1_full {term : Alg.Assertion.Algebra} :
    term (Ty.Prod (Word 9) ctx8_tail) sha256_ctx8_type :=
  (unit >>> @buffer_empty_spec (Word 3) 5 Ty.Unit (Alg.Assertion.toCore term)) &&&
    (I (O (@literal_ctx8_increment64 (Alg.Assertion.toCore term)) >>> @literal_ctx8_no_carry term) &&&
      (I I H &&& O H >>> @literal_sha_256_block (Alg.Assertion.toCore term))).

Definition literal_ctx8_add1 {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type (Word 3)) sha256_ctx8_type :=
  @literal_ctx8_snoc (Alg.Assertion.toCore term) >>>
    case (@literal_ctx8_add1_full term) iden >>>
    (@literal_ctx8_verify_count term &&& iden) >>> I H.

Lemma literal_ctx8_add1_algebra_matches term : @literal_ctx8_add1 term = @ctx8_add1_spec term.
Proof.
  unfold literal_ctx8_add1. rewrite literal_ctx8_snoc_matches, literal_ctx8_verify_count_matches.
  unfold ctx8_add1_spec, literal_ctx8_add1_full, ctx8_add1_full.
  rewrite literal_ctx8_increment64_matches, literal_sha_256_block_core_matches. reflexivity.
Qed.

Lemma literal_ctx8_add1_matches : @literal_ctx8_add1 optalg = @ctx8_add1_spec optalg.
Proof.
  unfold literal_ctx8_add1. rewrite literal_ctx8_snoc_matches, literal_ctx8_verify_count_matches.
  unfold ctx8_add1_spec, literal_ctx8_add1_full, ctx8_add1_full.
  rewrite literal_ctx8_increment64_matches, literal_sha_block_option_matches. reflexivity.
Qed.

(** The same canonical sequential composition for every vector depth. *)
Fixpoint literal_ctx8_addn n {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type (Vector (Word 3) n)) sha256_ctx8_type :=
  match n with
  | Datatypes.O => @literal_ctx8_add1 term
  | Datatypes.S k => (O H &&& I O H >>> @literal_ctx8_addn k term) &&& I I H >>> @literal_ctx8_addn k term
  end.

Lemma literal_ctx8_addn_algebra_matches n term : @literal_ctx8_addn n term = @ctx8_addn_spec n term.
Proof.
  induction n as [|n IHn]; [exact (literal_ctx8_add1_algebra_matches term)|].
  cbn [literal_ctx8_addn ctx8_addn_spec]. rewrite IHn. reflexivity.
Qed.

Lemma literal_ctx8_addn_matches n : @literal_ctx8_addn n optalg = @ctx8_addn_spec n optalg.
Proof.
  induction n as [|n IHn]; [exact literal_ctx8_add1_matches|].
  cbn [literal_ctx8_addn ctx8_addn_spec]. rewrite IHn. reflexivity.
Qed.

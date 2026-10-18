(** Final public equivalence with division's literal canonical-add calls. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jets_secp C.jet_secp_normalize_local C.jet_secp_canonical_normalize.
Require Import C.jet_multiply_spec C.jet_literal_division_add.
Require Import C.jet_secp_canonical_negate C.jet_secp_negate_local.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_fe_normalize512 {term : Alg.Core.Algebra} :
    term (Word 9) (Word 8) :=
  iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word))
    >>> @literal_modulo_word_spec 9 term >>> I H.
Definition literal_fe_multiply {term : Alg.Core.Algebra} :
    term (Ty.Prod (Word 8) (Word 8)) (Word 8) :=
  @multiply_word_spec 8 term >>> @literal_fe_normalize512 term.
Definition literal_fe_negate {term : Alg.Core.Algebra} :
    term (Word 8) (Word 8) :=
  Alg.scribe canonical_negate_factor &&& iden >>> @literal_fe_multiply term.

Lemma literal_fe_normalize512_matches :
  @literal_fe_normalize512 Alg.CoreFunSem = @canonical_fe_normalize512 Alg.CoreFunSem.
Proof.
  unfold literal_fe_normalize512, canonical_fe_normalize512.
  rewrite literal_modulo_matches. reflexivity.
Qed.
Lemma literal_fe_multiply_matches :
  @literal_fe_multiply Alg.CoreFunSem = @canonical_fe_multiply Alg.CoreFunSem.
Proof.
  unfold literal_fe_multiply, canonical_fe_multiply.
  rewrite literal_fe_normalize512_matches. reflexivity.
Qed.
Lemma literal_fe_negate_matches :
  @literal_fe_negate Alg.CoreFunSem = @canonical_fe_negate Alg.CoreFunSem.
Proof.
  unfold literal_fe_negate, canonical_fe_negate.
  rewrite literal_fe_multiply_matches. reflexivity.
Qed.

Theorem fe_negate_literal_local_spec :
  secp_jet_local_spec f_simplicity_fe_negate (Word 8) (Word 8)
    (@literal_fe_negate Alg.CoreFunSem).
Proof.
  rewrite literal_fe_negate_matches. exact fe_negate_local_spec.
Qed.
Print Assumptions fe_negate_literal_local_spec.

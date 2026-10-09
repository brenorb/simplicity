(** Literal canonical field-add structure, sharing the reviewed add and
    normalization ports. No standalone C jet equivalence is claimed here. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_canonical_add_adapter.
Require Import C.jet_secp_negate_literal_contract C.jet_literal_division_parametric.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_fe_one256 {term : Alg.Core.Algebra} : term Ty.Unit (Word 8) :=
  Bit.true >>> @left_pad_low_1_n term 8.

Definition literal_fe_add_expand {term : Alg.Core.Algebra} :
    term (Ty.Prod Bit (Word 8)) (Word 9) :=
  Bit.cond ((unit >>> @literal_fe_one256 term) &&& iden)
    ((unit >>> @Word.zero 8 term) &&& iden).

Definition literal_fe_add {term : Alg.Core.Algebra} :
    term (Ty.Prod (Word 8) (Word 8)) (Word 8) :=
  @canonical_add_word 8 term >>> @literal_fe_add_expand term
    >>> @literal_fe_normalize512 term.

Lemma literal_fe_one256_parametric : Alg.Core.Parametric (@literal_fe_one256).
Proof.
  intros term1 term2 R. unfold literal_fe_one256.
  apply Alg.comp_Parametric;
    [apply Bit.true_Parametric|apply left_pad_low_1_n_parametric].
Qed.

Lemma literal_fe_add_expand_parametric : Alg.Core.Parametric (@literal_fe_add_expand).
Proof.
  intros term1 term2 R. unfold literal_fe_add_expand.
  apply Bit.cond_Parametric; apply Alg.pair_Parametric;
    [apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply literal_fe_one256_parametric]
    |apply Alg.iden_Parametric
    |apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Word.zero_Parametric]
    |apply Alg.iden_Parametric].
Qed.

Lemma literal_fe_add_parametric : Alg.Core.Parametric (@literal_fe_add).
Proof.
  intros term1 term2 R. unfold literal_fe_add.
  apply Alg.comp_Parametric.
  - apply canonical_add_word_parametric.
  - apply Alg.comp_Parametric;
      [apply literal_fe_add_expand_parametric|apply literal_fe_normalize512_parametric].
Qed.
Print Assumptions literal_fe_one256_parametric.
Print Assumptions literal_fe_add_expand_parametric.
Print Assumptions literal_fe_add_parametric.

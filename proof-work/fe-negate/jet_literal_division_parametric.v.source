(** Literal-add division and field negation are algebra-independent programs. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_order_spec C.jet_subtract_spec C.jet_multiply_spec.
Require Import C.jet_complement_spec C.jet_test_value_spec C.jet_predicate_spec.
Require Import C.jet_division_core_spec C.jet_division_normalize_spec.
Require Import C.jet_canonical_add_adapter C.jet_literal_division_add.
Require Import C.jet_secp_negate_literal_contract.
Set Default Timeout 10.

Ltac literal_division_parametric :=
  repeat first [assumption | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric |
    apply Alg.unit_Parametric | apply Bit.cond_Parametric | apply Bit.and_Parametric |
    apply Bit.or_Parametric | apply Bit.not_Parametric | apply Bit.false_Parametric |
    apply Bit.true_Parametric | apply Word.zero_Parametric | apply Word.fill_Parametric |
    apply Word.fullAdder_Parametric | apply Word.fullMultiplier_Parametric |
    apply complement_spec_parametric | apply canonical_add_word_parametric | apply Word.leftmost_Parametric |
    apply division_high_word_parametric | apply lt_word_spec_parametric |
    apply subtract_word_spec_parametric | apply decrement_word_spec_parametric |
    apply multiply_word_spec_parametric].

Lemma literal_builder_parametric n {term1 term2 : Alg.Core.Algebra}
    (R : Alg.Core.Parametric.Rel term1 term2) rec1 rec2 :
  R _ _ rec1 rec2 ->
  R _ _ (@literal_div3n2n_word_builder n term1 rec1) (@literal_div3n2n_word_builder n term2 rec2).
Proof.
  intros Hrec. unfold literal_div3n2n_word_builder, literal_div3n2n_approx_spec,
    literal_div3n2n_body_spec, literal_div3n2n_loop0_spec,
    literal_div3n2n_loop1_spec, literal_div3n2n_loop2_spec.
  literal_division_parametric.
Qed.
Lemma literal_div2n1n_parametric n : Alg.Core.Parametric (@literal_div2n1n_word_spec n).
Proof.
  intros term1 term2 R. induction n as [|n IH].
  - apply div2n1n_bit_spec_parametric.
  - cbn [literal_div2n1n_word_spec]. literal_division_parametric.
    all: apply literal_builder_parametric; exact IH.
Qed.
Lemma literal_div_mod_parametric n : Alg.Core.Parametric (@literal_div_mod_word_spec n).
Proof.
  intros term1 term2 R. unfold literal_div_mod_word_spec. literal_division_parametric.
  all: first [apply literal_div2n1n_parametric | apply division_pre_shift_spec_parametric |
    apply division_post_shift_spec_parametric | apply predicate_spec_parametric].
Qed.
Lemma literal_modulo_parametric n : Alg.Core.Parametric (@literal_modulo_word_spec n).
Proof.
  intros term1 term2 R. apply Alg.comp_Parametric;
    [apply literal_div_mod_parametric|apply Alg.drop_Parametric, Alg.iden_Parametric].
Qed.
Lemma literal_fe_normalize512_parametric : Alg.Core.Parametric (@literal_fe_normalize512).
Proof.
  intros term1 term2 R. unfold literal_fe_normalize512.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.iden_Parametric|].
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|].
    apply Alg.pair_Parametric; [apply Word.zero_Parametric|apply Alg.scribe_Parametric].
  - apply Alg.comp_Parametric; [apply literal_modulo_parametric|].
    apply Alg.drop_Parametric, Alg.iden_Parametric.
Qed.
Lemma literal_fe_multiply_parametric : Alg.Core.Parametric (@literal_fe_multiply).
Proof.
  intros term1 term2 R. unfold literal_fe_multiply.
  apply Alg.comp_Parametric; [apply multiply_word_spec_parametric|
    apply literal_fe_normalize512_parametric].
Qed.
Lemma literal_fe_negate_parametric : Alg.Core.Parametric (@literal_fe_negate).
Proof.
  intros term1 term2 R. unfold literal_fe_negate.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.scribe_Parametric|apply Alg.iden_Parametric].
  - apply literal_fe_multiply_parametric.
Qed.
Print Assumptions literal_fe_negate_parametric.

(** Literal point programs are algebra-parametric, not arbitrary functions. *)
Require Import Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_gej_negate_literal C.jet_literal_division_parametric.
Require Import C.jet_secp_canonical_normalize C.jet_subtract_spec.
Set Default Timeout 10.

Lemma point_fe_normalize_parametric : Alg.Core.Parametric (@canonical_fe_normalize).
Proof.
  intros term1 term2 R; unfold canonical_fe_normalize.
  repeat first [assumption | apply subtract_word_spec_parametric |
    apply Alg.scribe_Parametric | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric |
    apply Alg.unit_Parametric | apply Bit.cond_Parametric].
Qed.

Lemma literal_ge_negate_parametric : Alg.Core.Parametric (@literal_ge_negate).
Proof.
  intros term1 term2 R; unfold literal_ge_negate.
  apply Alg.pair_Parametric.
  - apply Alg.take_Parametric; apply point_fe_normalize_parametric.
  - apply Alg.drop_Parametric; apply literal_fe_negate_parametric.
Qed.
Lemma literal_gej_negate_parametric : Alg.Core.Parametric (@literal_gej_negate).
Proof.
  intros term1 term2 R; unfold literal_gej_negate.
  apply Alg.pair_Parametric.
  - apply Alg.take_Parametric; apply literal_ge_negate_parametric.
  - apply Alg.drop_Parametric; apply point_fe_normalize_parametric.
Qed.
Print Assumptions literal_ge_negate_parametric.
Print Assumptions literal_gej_negate_parametric.

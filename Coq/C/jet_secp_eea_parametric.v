(** Algebra-independent EEA and inversion programs: the bridges are about
    fixed Simplicity terms, not only functions in one interpretation. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_eea_literal C.jet_secp_invert_literal C.jet_order_spec
 C.jet_test_value_spec C.jet_extend_word_spec C.jet_literal_division_parametric.
Set Default Timeout 10.

Local Ltac eea_core :=
 lazymatch goal with
 | |- _ _ _ (@Alg.Core.Combinators.comp _ _ _ _ _ _) _ => apply Alg.comp_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.pair _ _ _ _ _ _) _ => apply Alg.pair_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.take _ _ _ _ _) _ => apply Alg.take_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.drop _ _ _ _ _) _ => apply Alg.drop_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.injl _ _ _ _ _) _ => apply Alg.injl_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.injr _ _ _ _ _) _ => apply Alg.injr_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.iden _ _) _ => apply Alg.iden_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.unit _ _) _ => apply Alg.unit_Parametric
 end.

Lemma literal_eea_row_step_parametric n : Alg.Core.Parametric (@literal_eea_row_step n).
Proof.
 intros t1 t2 R;unfold literal_eea_row_step.
 repeat first [eea_core | apply literal_div_mod_parametric | apply Word.fullMultiplier_Parametric | apply Word.zero_Parametric].
Qed.
Lemma literal_eea_step_parametric n : Alg.Core.Parametric (@literal_eea_step n).
Proof.
 intros t1 t2 R;unfold literal_eea_step.
 repeat first [eea_core | apply Bit.cond_Parametric | apply lt_word_spec_parametric | apply literal_eea_row_step_parametric].
Qed.
Lemma literal_eea_iterate_parametric n depth : Alg.Core.Parametric (@literal_eea_iterate n depth).
Proof.
 intros t1 t2 R;induction depth;cbn [literal_eea_iterate];
   apply Alg.comp_Parametric;first [assumption|apply literal_eea_step_parametric].
Qed.
Lemma literal_eea_one_parametric n : Alg.Core.Parametric (@literal_eea_one n).
Proof.
 intros t1 t2 R;unfold literal_eea_one;apply Alg.comp_Parametric;
   [apply Bit.true_Parametric|exact (left_pad_word_spec_parametric 0 n Datatypes.false t1 t2 R)].
Qed.
Lemma literal_eea_pre_parametric n : Alg.Core.Parametric (@literal_eea_pre n).
Proof.
 intros t1 t2 R;unfold literal_eea_pre.
 repeat first [eea_core | apply literal_eea_one_parametric | apply Word.zero_Parametric].
Qed.
Lemma literal_eea_post_parametric n : Alg.Core.Parametric (@literal_eea_post n).
Proof.
 intros t1 t2 R;unfold literal_eea_post.
 repeat first [eea_core | apply Bit.cond_Parametric | apply is_zero_word_spec_parametric].
Qed.
Lemma literal_eea_parametric n : Alg.Core.Parametric (@literal_eea n).
Proof.
 intros t1 t2 R;unfold literal_eea.
 repeat first [eea_core | apply literal_eea_pre_parametric | apply literal_eea_iterate_parametric | apply literal_eea_post_parametric].
Qed.
Lemma literal_bezout_parametric n : Alg.Core.Parametric (@literal_bezout n).
Proof.
 intros t1 t2 R;unfold literal_bezout.
 repeat first [eea_core | apply literal_eea_parametric].
Qed.

Lemma literal_inverse_body_parametric W p {t1 t2 : Alg.Core.Algebra}
 (R : Alg.Core.Parametric.Rel t1 t2) b1 b2 neg1 neg2 :
 R _ _ b1 b2 -> R _ _ neg1 neg2 ->
 R _ _ (@literal_inverse_body W t1 p b1 neg1) (@literal_inverse_body W t2 p b2 neg2).
Proof.
 intros HB HN;unfold literal_inverse_body.
 repeat first [assumption | eea_core | apply Alg.copair_Parametric | apply Alg.scribe_Parametric].
Qed.
Lemma literal_fe_invert_parametric : Alg.Core.Parametric (@literal_fe_invert).
Proof.
 intros t1 t2 R;unfold literal_fe_invert.
 apply literal_inverse_body_parametric;[apply literal_bezout_parametric|apply literal_fe_negate_parametric].
Qed.

(** Literal hash_to_curve_core from LibSecp256k1.hs:729--742, using the
    already-reviewed SHA, comparison, SWU, addition and normalization terms.
    Relate the original C call's retained affine evidence to that program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_order_spec C.jet_secp_fe_math C.jet_secp_field_cmov
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_square_columns
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_fe_inv_prefix C.jet_secp_invert_literal
 C.jet_secp_rescale_literal C.jet_secp_gej_norm_output C.jet_secp_gej_norm_literal
 C.jet_secp_gej_norm_branch C.jet_secp_swu_literal C.jet_secp_add_literal
 C.jet_secp_literal_add_program C.jet_secp_generator_hash_literal C.jet_secp_generator_hash_map
 C.jet_secp_generator_affine_roundtrip C.jet_secp_hash_public_call.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Opaque literal_generator_hash literal_swu literal_gej_ge_add literal_gej_normalize
 literal_gej_norm canonical_fe_is_zero lt_word_spec rescale_field_output canonical_field_word.

Definition literal_hash_accept {term:Alg.Core.Algebra} :
 term (Ty.Prod (Word 8) (Word 8)) Bit :=
 Bit.and ((O H &&& Alg.scribe canonical_field_word) >>> @lt_word_spec term 8)
         ((I H &&& Alg.scribe canonical_field_word) >>> @lt_word_spec term 8).
Definition literal_hash_point_sum {term:Alg.Core.Algebra} :
 term (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) :=
 ((O (@literal_swu term) &&& (unit >>> @literal_fe_one256 term)) &&& I (@literal_swu term))
   >>> @literal_gej_ge_add term.
Definition literal_hash_to_curve_core {term:Alg.Core.Algebra} :
 term (Word 8) (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 8))) :=
 (@literal_generator_hash Datatypes.false term &&& @literal_generator_hash Datatypes.true term)
   >>> (@literal_hash_accept term &&& iden)
   >>> Bit.cond (@literal_hash_point_sum term >>> @literal_gej_normalize term) (injl unit).

Lemma literal_hash_accept_parametric : Alg.Core.Parametric (@literal_hash_accept).
Proof.
 intros t1 t2 R;unfold literal_hash_accept;apply Bit.and_Parametric.
 - apply Alg.comp_Parametric.
   + apply Alg.pair_Parametric;[apply Alg.take_Parametric;apply Alg.iden_Parametric|apply Alg.scribe_Parametric].
   + apply lt_word_spec_parametric.
 - apply Alg.comp_Parametric.
   + apply Alg.pair_Parametric;[apply Alg.drop_Parametric;apply Alg.iden_Parametric|apply Alg.scribe_Parametric].
   + apply lt_word_spec_parametric.
Qed.
Lemma literal_hash_point_sum_parametric : Alg.Core.Parametric (@literal_hash_point_sum).
Proof.
 intros t1 t2 R;unfold literal_hash_point_sum;apply Alg.comp_Parametric.
 - apply Alg.pair_Parametric.
   + apply Alg.pair_Parametric.
     * apply Alg.take_Parametric;apply literal_swu_parametric.
     * apply Alg.comp_Parametric;[apply Alg.unit_Parametric|apply literal_fe_one256_parametric].
   + apply Alg.drop_Parametric;apply literal_swu_parametric.
 - apply literal_gej_ge_add_parametric.
Qed.
Lemma literal_hash_to_curve_core_parametric : Alg.Core.Parametric (@literal_hash_to_curve_core).
Proof.
 intros t1 t2 R;unfold literal_hash_to_curve_core;apply Alg.comp_Parametric.
 - apply Alg.pair_Parametric;apply literal_generator_hash_parametric.
 - apply Alg.comp_Parametric.
   + apply Alg.pair_Parametric;[apply literal_hash_accept_parametric|apply Alg.iden_Parametric].
   + apply Bit.cond_Parametric.
     * apply Alg.comp_Parametric;[apply literal_hash_point_sum_parametric|apply literal_gej_normalize_parametric].
     * apply Alg.injl_Parametric;apply Alg.unit_Parametric.
Qed.

Lemma literal_hash_accept_value (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_hash_accept Alg.CoreFunSem (x,y))=
   andb (@toZ (WordToZ 8) x <? feP) (@toZ (WordToZ 8) y <? feP).
Proof.
 unfold literal_hash_accept.
 change (Bit.toBool (match @lt_word_spec Alg.CoreFunSem 8
   (x,@Alg.scribe (Ty.Prod (Word 8) (Word 8)) (Word 8) canonical_field_word Alg.CoreFunSem (x,y)) with
   | inl _=>inl tt
   | inr _=>@lt_word_spec Alg.CoreFunSem 8
       (y,@Alg.scribe (Ty.Prod (Word 8) (Word 8)) (Word 8) canonical_field_word Alg.CoreFunSem (x,y)) end)=
   andb (@toZ (WordToZ 8) x <? feP) (@toZ (WordToZ 8) y <? feP)).
 rewrite !Alg.scribe_correct.
 pose proof (lt_word_spec_numeric 8 x canonical_field_word) as X.
 pose proof (lt_word_spec_numeric 8 y canonical_field_word) as Y.
 rewrite canonical_field_word_value,canonical_field_order_matches_limb_model in X,Y.
 rewrite <-X,<-Y.
 destruct (@lt_word_spec Alg.CoreFunSem 8 (x,canonical_field_word)) as [ [] | [] ];
 destruct (@lt_word_spec Alg.CoreFunSem 8 (y,canonical_field_word)) as [ [] | [] ];reflexivity.
Qed.
Lemma literal_hash_point_sum_value (x y:Ty.tySem (Word 8)) :
 @literal_hash_point_sum Alg.CoreFunSem (x,y)=
 @literal_gej_ge_add Alg.CoreFunSem
   ((@literal_swu Alg.CoreFunSem x,@literal_fe_one256 Alg.CoreFunSem tt),@literal_swu Alg.CoreFunSem y).
Proof. reflexivity. Qed.
Lemma literal_hash_to_curve_core_value (key:Ty.tySem (Word 8)) :
 @literal_hash_to_curve_core Alg.CoreFunSem key=
 if andb (generator_hash_accepted Datatypes.false key) (generator_hash_accepted Datatypes.true key)
 then @literal_gej_normalize Alg.CoreFunSem
   (@literal_hash_point_sum Alg.CoreFunSem
     (@literal_generator_hash Datatypes.false Alg.CoreFunSem key,@literal_generator_hash Datatypes.true Alg.CoreFunSem key))
 else inl tt.
Proof.
 unfold literal_hash_to_curve_core.
 change ((match @literal_hash_accept Alg.CoreFunSem
   (@literal_generator_hash Datatypes.false Alg.CoreFunSem key,@literal_generator_hash Datatypes.true Alg.CoreFunSem key) with
   | inl _=>inl tt
   | inr _=>@literal_gej_normalize Alg.CoreFunSem
     (@literal_hash_point_sum Alg.CoreFunSem
       (@literal_generator_hash Datatypes.false Alg.CoreFunSem key,@literal_generator_hash Datatypes.true Alg.CoreFunSem key)) end)=
   if andb (generator_hash_accepted Datatypes.false key) (generator_hash_accepted Datatypes.true key)
   then @literal_gej_normalize Alg.CoreFunSem
     (@literal_hash_point_sum Alg.CoreFunSem
       (@literal_generator_hash Datatypes.false Alg.CoreFunSem key,@literal_generator_hash Datatypes.true Alg.CoreFunSem key))
   else inl tt).
 pose proof (literal_hash_accept_value (@literal_generator_hash Datatypes.false Alg.CoreFunSem key)
   (@literal_generator_hash Datatypes.true Alg.CoreFunSem key)) as Accepted.
 fold (generator_hash_accepted Datatypes.false key) (generator_hash_accepted Datatypes.true key) in Accepted.
 destruct (@literal_hash_accept Alg.CoreFunSem
   (@literal_generator_hash Datatypes.false Alg.CoreFunSem key,@literal_generator_hash Datatypes.true Alg.CoreFunSem key)) as [ [] | [] ];
   cbn [Bit.toBool] in Accepted;rewrite <-Accepted;reflexivity.
Qed.

Lemma hash_public_finite_literal key sx sy sz flag ox oy :
 hash_public_value key sx sy sz flag ox oy ->flag=Int.zero ->
 (rescale_field_output ox,rescale_field_output oy)=
   @literal_gej_norm Alg.CoreFunSem ((rescale_field_output sx,rescale_field_output sy),rescale_field_output sz).
Proof.
 intros (_ & _ & _ & _ & _ & _ & _ & Finite & _) Zero.
 destruct (Finite Zero) as (zi & Inverse & X & Y & VX & VY).
 eapply affine_normalized_words_literal with (x:=sx) (y:=sy) (zi:=zi).
 - rewrite rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
 - rewrite rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
 - rewrite Inverse,rescale_field_output_value,field_prime_matches_normalizer;reflexivity.
 - rewrite field_prime_matches_normalizer;exact VX.
 - rewrite field_prime_matches_normalizer;exact VY.
Qed.

Lemma hash_public_infinite_literal_zero key sx sy sz flag ox oy :
 hash_public_value key sx sy sz flag ox oy ->flag<>Int.zero ->
 @toZ (WordToZ 8) (rescale_field_output ox)=0 /\ @toZ (WordToZ 8) (rescale_field_output oy)=0.
Proof.
 intros (_ & _ & _ & _ & _ & _ & _ & _ & Infinite) Nonzero.
 destruct (Infinite Nonzero) as [-> ->];split;apply generator_infinite_output_zero.
Qed.

(** Exhaustive comparison with the core specification, retaining rejection
    and infinity rather than restricting the public input to a finite sum. *)
Theorem hash_public_core_result key sx sy sz flag ox oy :
 hash_public_value key sx sy sz flag ox oy ->
 @literal_hash_to_curve_core Alg.CoreFunSem key=
 if andb (generator_hash_accepted Datatypes.false key) (generator_hash_accepted Datatypes.true key)
 then if Int.eq flag Int.zero
      then inr (rescale_field_output ox,rescale_field_output oy) else inl tt
 else inl tt.
Proof.
 intro Value;rewrite literal_hash_to_curve_core_value.
 destruct (andb (generator_hash_accepted Datatypes.false key)
   (generator_hash_accepted Datatypes.true key)) eqn:Accepted;[|reflexivity].
 apply Bool.andb_true_iff in Accepted;destruct Accepted as [Good0 Good1].
 pose proof Value as (_ & _ & _ & Flag & Point & _).
 rewrite literal_hash_point_sum_value,<-(Point Good0 Good1),literal_gej_normalize_value.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output sz))) eqn:Zero.
 - change (flag=Int.one) in Flag;rewrite Flag;reflexivity.
 - change (flag=Int.zero) in Flag;rewrite Flag,Int.eq_true.
   f_equal;symmetry;exact (hash_public_finite_literal _ _ _ _ _ _ _ Value Flag).
Qed.

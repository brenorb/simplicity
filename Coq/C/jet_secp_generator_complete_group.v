(** Group interpretation of the original two-stream generator, including zero. *)
From Coq Require Import ZArith Lia List.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_word_group C.jet_secp_curve_group
 C.jet_secp_curve_group_sign C.jet_secp_curve_group_power C.jet_secp_lookup5_group
 C.jet_secp_signed_group_action C.jet_secp_jacobian_word_group
 C.jet_secp_strauss_group C.jet_secp_strauss_scalar_group C.jet_secp_strauss_window_values
 C.jet_secp_generate_small_group C.jet_secp_generate_group C.jet_secp_generate_literal C.jet_secp_generator_program
 C.jet_secp_generate_program C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array
 C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_literal_values C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf15_reconstruction C.jet_secp_literal_infinity
 C.jet_secp_double_literal C.jet_secp_add_literal C.jet_secp_canonical_scalar
 C.jet_secp_scalar_split128_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_double literal_gej_ge_add literal_generate_small
 literal_generator_step literal_generator_digits129 literal_generate literal_scalar_split128
 canonical_scalar_normalize literal_wnaf15 literal_wnaf_flatten secp_group_signed_power SMain.add EGroup.gpow
 secp_group_generator secp_curve_group.
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Definition secp_generator_digit_group (a:secp_group_point)
 (ds:Ty.tySem (Ty.Prod literal_wnaf_digit literal_wnaf_digit)):=
 secp_strauss_group_step secp_group_infinity a (inl tt) (inl tt) (fst ds) (snd ds).
Definition secp_generator_digit_valid
 (ds:Ty.tySem (Ty.Prod literal_wnaf_digit literal_wnaf_digit)):=
 wnaf_literal_valid (fst ds)/\wnaf_literal_valid (snd ds).
Theorem secp_literal_generator_step_group (point:Ty.tySem literal_generator_jacobian)
 (a:secp_group_point) (dg dh:Ty.tySem literal_wnaf_digit):
 secp_jacobian_word_rep (GZnZ.one feP) point a ->wnaf_literal_valid dg ->wnaf_literal_valid dh ->
 secp_jacobian_word_rep (GZnZ.one feP)
 (@literal_generator_step Alg.CoreFunSem (point,(dg,dh))) (secp_generator_digit_group a (dg,dh)).
Proof.
 intros Start ValidG ValidH.
 assert (Unit:GZnZ.one feP<>GZnZ.zero feP).
 { discriminate. }
 set (doubled:=@literal_gej_double Alg.CoreFunSem point).
 assert (Double:secp_jacobian_word_rep (GZnZ.one feP) doubled (a⊕a)).
 { unfold doubled;destruct point as [[x y] z];apply secp_literal_double_group;exact Start. }
 set (low:=match dg with inl _=>doubled
  |inr word=>@literal_gej_ge_add Alg.CoreFunSem (doubled,@literal_generate_small Datatypes.false Alg.CoreFunSem word) end).
 set (lowP:=match dg with inl _=>a⊕a
  |inr word=>(a⊕a)⊕secp_group_signed_power secp_group_generator (1*literal_wnaf_signed16 word) end).
 assert (Low:secp_jacobian_word_rep (GZnZ.one feP) low lowP).
 { unfold low,lowP;destruct dg as [u|word].
   - exact Double.
   - apply secp_literal_mixed_group_output;[exact Unit|exact Double|].
     exact (secp_literal_generate_small_valid_group Datatypes.false word ValidG). }
 rewrite literal_generator_step_value;cbn zeta;fold doubled low.
 unfold secp_generator_digit_group,secp_strauss_group_step;cbn [fst snd];fold lowP.
 destruct dh as [u|word].
 - exact Low.
 - apply secp_literal_mixed_group_output;[exact Unit|exact Low|].
   exact (secp_literal_generate_small_valid_group Datatypes.true word ValidH).
Qed.
Theorem secp_literal_generator_fold_group
 (digits:list (Ty.tySem (Ty.Prod literal_wnaf_digit literal_wnaf_digit))):
 Forall secp_generator_digit_valid digits ->
 forall (point:Ty.tySem literal_generator_jacobian) (a:secp_group_point),
 secp_jacobian_word_rep (GZnZ.one feP) point a ->
 secp_jacobian_word_rep (GZnZ.one feP)
 (fold_left (fun point ds=>@literal_generator_step Alg.CoreFunSem (point,ds)) digits point)
 (fold_left secp_generator_digit_group digits a).
Proof.
 intro Valid;induction Valid as [|digit digits Good Valid IH];intros point a Start;[exact Start|].
 destruct digit as [dg dh];destruct Good as [GoodG GoodH];cbn [fold_left].
 apply IH;apply secp_literal_generator_step_group;assumption.
Qed.
Definition secp_generator_pair_group (c:Z*Z):secp_group_point:=
 secp_group_signed_power secp_group_generator (fst c)⊕
 secp_group_signed_power (EGroup.gpow secp_group_generator secp_curve_group (2^128)) (snd c).
Definition secp_generator_pair_step (c:Z*Z)
 (ds:Ty.tySem (Ty.Prod literal_wnaf_digit literal_wnaf_digit)):=
 (2*fst c+wnaf_literal_value (fst ds),2*snd c+wnaf_literal_value (snd ds)).
Lemma secp_generator_pair_group_step c ds:
 secp_generator_digit_group (secp_generator_pair_group c) ds=
 secp_generator_pair_group (secp_generator_pair_step c ds).
Proof.
 destruct c as [a b],ds as [dg dh].
 pose proof (secp_strauss_combination_step secp_group_infinity ((0,0),(a,b))
  ((inl tt,inl tt),(dg,dh))) as Step.
 unfold secp_strauss_combination in Step.
 cbn [fst snd secp_strauss_coefficient_step secp_strauss_coeff_add secp_strauss_digit_coefficients wnaf5_literal_value] in Step;rewrite !secp_generator_signed_zero,!SMain.add_0_l in Step.
 replace (a+a) with (2*a) in Step by ring.
 replace (b+b) with (2*b) in Step by ring.
 change (secp_generator_digit_group (secp_generator_pair_group (a,b)) (dg,dh)=
 secp_generator_pair_group (secp_generator_pair_step (a,b) (dg,dh))) in Step;exact Step.
Qed.
Lemma secp_generator_pair_fold digits c:
 fold_left secp_generator_digit_group digits (secp_generator_pair_group c)=
 secp_generator_pair_group (fold_left secp_generator_pair_step digits c).
Proof.
 revert c;induction digits as [|digit digits IH];intro c;[reflexivity|].
 cbn [fold_left];rewrite secp_generator_pair_group_step;apply IH.
Qed.
Lemma secp_generator_pair_zero:secp_generator_pair_group (0,0)=secp_group_infinity.
Proof.
 unfold secp_generator_pair_group;cbn [fst snd];rewrite !secp_generator_signed_zero;apply SMain.add_0_l.
Qed.
Lemma secp_generator_pair_values digits a b:
 fold_left secp_generator_pair_step digits (a,b)=
 (fold_left secp_wnaf15_digit_fold (map fst digits) a,
  fold_left secp_wnaf15_digit_fold (map snd digits) b).
Proof.
 revert a b;induction digits as [|digit digits IH];intros a b;[reflexivity|].
 destruct digit as [dg dh];cbn [fold_left map secp_generator_pair_step fst snd secp_wnaf15_digit_fold];apply IH.
Qed.
Lemma secp_generator_combined_valid (g h:list (Ty.tySem literal_wnaf_digit)):
 Forall wnaf_literal_valid g ->Forall wnaf_literal_valid h ->
 Forall secp_generator_digit_valid (combine g h).
Proof.
 intros GoodG GoodH;apply Forall_forall;intros [dg dh] Member;split.
 - apply (proj1 (Forall_forall _ _) GoodG);exact (in_combine_l _ _ _ _ Member).
 - apply (proj1 (Forall_forall _ _) GoodH);exact (in_combine_r _ _ _ _ Member).
Qed.
Theorem secp_literal_generator_window_group (gl gh:Ty.tySem (Word 7)):
 secp_jacobian_word_rep (GZnZ.one feP)
 (@literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
  (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl),@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh))))
 (secp_generator_pair_group (@toZ (WordToZ 7) gl,@toZ (WordToZ 7) gh)).
Proof.
 pose proof (literal_wnaf15_values gl) as GoodG;pose proof (literal_wnaf15_values gh) as GoodH.
 pose proof (secp_wnaf15_digits_reconstruct gl) as ValueG.
 pose proof (secp_wnaf15_digits_reconstruct gh) as ValueH.
 unfold literal_wnaf15_digits in ValueG,ValueH.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl)) as [hg tg] eqn:WG.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh)) as [hh th] eqn:WH.
 assert (ValidG:Forall wnaf_literal_valid (hg::literal_wnaf_flatten 7 tg)).
 { exact (eq_ind (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl))
   (fun result:Ty.tySem (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))=>
    Forall wnaf_literal_valid (let '(top,rest):=result in top::literal_wnaf_flatten 7 rest)) GoodG (hg,tg) WG). }
 assert (ValidH:Forall wnaf_literal_valid (hh::literal_wnaf_flatten 7 th)).
 { exact (eq_ind (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh))
   (fun result:Ty.tySem (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))=>
    Forall wnaf_literal_valid (let '(top,rest):=result in top::literal_wnaf_flatten 7 rest)) GoodH (hh,th) WH). }
 rewrite literal_generator_digits129_list.
 set (digits:=(hg,hh)::combine (literal_wnaf_flatten 7 tg) (literal_wnaf_flatten 7 th)).
 assert (Valid:Forall secp_generator_digit_valid digits).
 { constructor.
   - split;[exact (Forall_inv ValidG)|exact (Forall_inv ValidH)].
   - apply secp_generator_combined_valid;[exact (Forall_inv_tail ValidG)|exact (Forall_inv_tail ValidH)]. }
 assert (Lengths:length (literal_wnaf_flatten 7 tg)=length (literal_wnaf_flatten 7 th)).
 { rewrite !literal_wnaf_flatten_length;reflexivity. }
 destruct (secp_combine_maps _ _ Lengths) as [Left Right].
 assert (Values:fold_left secp_generator_pair_step digits (0,0)=
  (@toZ (WordToZ 7) gl,@toZ (WordToZ 7) gh)).
 { rewrite secp_generator_pair_values;unfold digits;cbn [map fst snd];apply f_equal2.
   - transitivity (fold_left secp_wnaf15_digit_fold (hg::literal_wnaf_flatten 7 tg) 0).
     + exact (f_equal (fun xs=>fold_left secp_wnaf15_digit_fold (hg::xs) 0) Left).
     + exact ValueG.
   - transitivity (fold_left secp_wnaf15_digit_fold (hh::literal_wnaf_flatten 7 th) 0).
     + exact (f_equal (fun xs=>fold_left secp_wnaf15_digit_fold (hh::xs) 0) Right).
     + exact ValueH. }
 pose proof (secp_literal_generator_fold_group digits Valid
  (@literal_gej_infinity Alg.CoreFunSem tt) secp_group_infinity
  (secp_literal_infinity_group (GZnZ.one feP))) as Fold.
 rewrite <-secp_generator_pair_zero,secp_generator_pair_fold,Values in Fold;exact Fold.
Qed.
Theorem secp_literal_generate_group (ng:Ty.tySem (Word 8)):
 secp_jacobian_word_rep (GZnZ.one feP) (@literal_generate Alg.CoreFunSem ng)
 (secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))).
Proof.
 rewrite literal_generate_value.
 pose proof (secp_literal_generator_window_group (literal_split128_low ng) (literal_split128_high ng)) as Generated.
 unfold secp_generator_pair_group in Generated;cbn [fst snd] in Generated.
 rewrite (secp_generator_base_signed_action Datatypes.true (@toZ (WordToZ 7) (literal_split128_high ng))) in Generated.
 rewrite <-secp_group_signed_power_add in Generated.
 assert (Rebuild:@toZ (WordToZ 7) (literal_split128_low ng)+2^128*@toZ (WordToZ 7) (literal_split128_high ng)=
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)).
 { destruct (literal_scalar_split128_numeric ng) as [Low High];rewrite Low,High.
   pose proof (Z.div_mod (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)) (2^128) ltac:(lia));nia. }
 rewrite Rebuild in Generated;exact Generated.
Qed.

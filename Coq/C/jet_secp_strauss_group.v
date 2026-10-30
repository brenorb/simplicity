(** Interpret the original four-stream Strauss step and 129-step traversal. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_field_word_group C.jet_secp_jacobian_word_group
 C.jet_secp_jacobian_word_transforms C.jet_secp_jacobian_mixed_word_group C.jet_secp_table_pass2_group C.jet_secp_table_walk_group
 C.jet_secp_lookup5_group C.jet_secp_lookup5_literal C.jet_secp_generate_small_group
 C.jet_secp_wnaf_literal C.jet_secp_wnaf5_literal C.jet_secp_wnaf_literal_mask
 C.jet_secp_wnaf_literal_values C.jet_secp_scalar_lambda_global C.jet_secp_generate_literal
 C.jet_secp_strauss_program C.jet_secp_literal_add_program C.jet_secp_add_literal
 C.jet_secp_double_literal C.jet_secp_rescale_literal C.jet_secp_table_get_lambda_literal C.jet_secp_scalar_table_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_strauss_group_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque secp_field_word literal_gej_double literal_gej_ge_add literal_gej_ge_add_ex
 literal_lookup5 literal_ge_scale_lambda literal_generate_small literal_gej_zinv
 literal_strauss_step EGroup.gpow SMain.add.
Lemma secp_affine_share_context (z:Ty.tySem (Word 8)) (a:Ty.tySem literal_table_ge) (p:secp_group_point):
 secp_field_word z<>GZnZ.zero feP ->secp_affine_word_rep (GZnZ.one feP) a p ->
 secp_affine_word_rep (secp_field_word z) (@literal_gej_zinv Alg.CoreFunSem (a,z)) p.
Proof.
 intros Nonzero Represented;pose proof (secp_pass2_leaf_group (GZnZ.one feP) a z p Nonzero Represented) as Shared.
 assert (Unit:forall t:secp_group_field,GZnZ.mul feP (GZnZ.one feP) t=t).
 { intro t;unfold secp_group_field in *;ring. }
 rewrite Unit in Shared;exact Shared.
Qed.
Definition secp_strauss_group_step (p a:secp_group_point)
 (d1 dl:Ty.tySem literal_wnaf5_digit) (dg dh:Ty.tySem literal_wnaf_digit):=
 let doubled:=SMain.add secp_group_theory a a in
 let low:=match d1 with inl _=>doubled
 | inr nib=>SMain.add secp_group_theory doubled (secp_group_signed_power p (lookup5_digit nib)) end in
 let high:=match dl with inl _=>low
 | inr nib=>SMain.add secp_group_theory low
  (EGroup.gpow (secp_group_signed_power p (lookup5_digit nib)) secp_curve_group canonical_lambda_value) end in
 let gen:=match dg with inl _=>high
 | inr word=>SMain.add secp_group_theory high
  (secp_group_signed_power secp_group_generator (1*literal_wnaf_signed16 word)) end in
 match dh with inl _=>gen
 | inr word=>SMain.add secp_group_theory gen
  (secp_group_signed_power secp_group_generator (2^128*literal_wnaf_signed16 word)) end.
Lemma secp_literal_mixed_group_output (c:secp_group_field)
 (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge) (p q:secp_group_point):
 c<>GZnZ.zero feP ->secp_jacobian_word_rep c a p ->secp_affine_word_rep c b q ->
 secp_jacobian_word_rep c (@literal_gej_ge_add Alg.CoreFunSem (a,b)) (SMain.add secp_group_theory p q).
Proof. destruct a as [[x y] zz],b as [bx byword];apply secp_literal_mixed_group. Qed.
Local Ltac mixed_group:=apply secp_literal_mixed_group_output.
Theorem secp_literal_strauss_step_group (z:Ty.tySem (Word 8))
 (table:Ty.tySem (literal_table_vector 3)) (p a:secp_group_point)
 (point:Ty.tySem literal_generator_jacobian)
 (d1 dl:Ty.tySem literal_wnaf5_digit) (dg dh:Ty.tySem literal_wnaf_digit):
 secp_field_word z<>GZnZ.zero feP ->
 secp_table_vector_group 3 table (secp_group_odd_table p) (secp_field_word z) ->
 secp_jacobian_word_rep (secp_field_word z) point a ->
 wnaf_literal_valid dg ->wnaf_literal_valid dh ->
 secp_jacobian_word_rep (secp_field_word z)
  (@literal_strauss_step Alg.CoreFunSem (point,((z,table),((d1,dl),(dg,dh)))))
  (secp_strauss_group_step p a d1 dl dg dh).
Proof.
 intros Nonzero Table Start ValidG ValidH.
 set (doubled:=@literal_gej_double Alg.CoreFunSem point).
 assert (Double:secp_jacobian_word_rep (secp_field_word z) doubled (SMain.add secp_group_theory a a)).
 { unfold doubled;destruct point as [[x y] zz];apply secp_literal_double_group;exact Start. }
 set (low:=match d1 with inl _=>doubled
  | inr nib=>@literal_gej_ge_add Alg.CoreFunSem (doubled,@literal_lookup5 Alg.CoreFunSem (nib,table)) end).
 set (lowP:=match d1 with inl _=>SMain.add secp_group_theory a a
  | inr nib=>SMain.add secp_group_theory (SMain.add secp_group_theory a a)
   (secp_group_signed_power p (lookup5_digit nib)) end).
 assert (Low:secp_jacobian_word_rep (secp_field_word z) low lowP).
 { unfold low,lowP;destruct d1 as [u|nib].
   - exact Double.
   - mixed_group;[exact Nonzero|exact Double|apply secp_literal_lookup5_group;exact Table]. }
 set (high:=match dl with inl _=>low
  | inr nib=>@literal_gej_ge_add Alg.CoreFunSem
   (low,@literal_ge_scale_lambda Alg.CoreFunSem (@literal_lookup5 Alg.CoreFunSem (nib,table))) end).
 set (highP:=match dl with inl _=>lowP
  | inr nib=>SMain.add secp_group_theory lowP
   (EGroup.gpow (secp_group_signed_power p (lookup5_digit nib)) secp_curve_group canonical_lambda_value) end).
 assert (High:secp_jacobian_word_rep (secp_field_word z) high highP).
 { unfold high,highP;destruct dl as [u|nib].
   - exact Low.
   - mixed_group;[exact Nonzero|exact Low|apply secp_literal_lookup5_lambda_group;exact Table]. }
 set (gen:=match dg with inl _=>high
  | inr word=>@literal_gej_ge_add Alg.CoreFunSem
   (high,@literal_gej_zinv Alg.CoreFunSem (@literal_generate_small false Alg.CoreFunSem word,z)) end).
 set (genP:=match dg with inl _=>highP
  | inr word=>SMain.add secp_group_theory highP
   (secp_group_signed_power secp_group_generator (1*literal_wnaf_signed16 word)) end).
 assert (Gen:secp_jacobian_word_rep (secp_field_word z) gen genP).
 { unfold gen,genP;destruct dg as [u|word].
   - exact High.
   - mixed_group;[exact Nonzero|exact High|].
     apply secp_affine_share_context;[exact Nonzero|apply (secp_literal_generate_small_valid_group false word);exact ValidG]. }
 rewrite literal_strauss_step_value;cbn zeta;fold doubled low high gen.
 unfold secp_strauss_group_step;fold lowP highP genP.
 destruct dh as [u|word].
 - exact Gen.
 - mixed_group;[exact Nonzero|exact Gen|].
   apply secp_affine_share_context;[exact Nonzero|apply (secp_literal_generate_small_valid_group true word);exact ValidH].
Qed.
From Coq Require Import List.
Import ListNotations.
Definition secp_strauss_group_digit_step (p a:secp_group_point)
 (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)):=
 let '((d1,dl),(dg,dh)):=ds in secp_strauss_group_step p a d1 dl dg dh.
Definition secp_strauss_group_digit_valid
 (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)):=
 wnaf_literal_valid (fst (snd ds)) /\wnaf_literal_valid (snd (snd ds)).
Theorem secp_literal_strauss_fold_group (z:Ty.tySem (Word 8))
 (table:Ty.tySem (literal_table_vector 3)) (p:secp_group_point)
 (digits:list (Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))):
 secp_field_word z<>GZnZ.zero feP ->
 secp_table_vector_group 3 table (secp_group_odd_table p) (secp_field_word z) ->
 Forall secp_strauss_group_digit_valid digits ->
 forall (point:Ty.tySem literal_generator_jacobian) (a:secp_group_point),
 secp_jacobian_word_rep (secp_field_word z) point a ->
 secp_jacobian_word_rep (secp_field_word z)
 (fold_left (fun point ds=>@literal_strauss_step Alg.CoreFunSem (point,((z,table),ds))) digits point)
 (fold_left (secp_strauss_group_digit_step p) digits a).
Proof.
 intros Nonzero Table Valid;induction Valid as [|d digits Good Valid IH];intros point a Start;[exact Start|].
 destruct d as [[d1 dl] [dg dh]];destruct Good as [GoodG GoodH].
 cbn [fold_left secp_strauss_group_digit_step].
 apply IH;apply secp_literal_strauss_step_group;assumption.
Qed.
Lemma secp_strauss_combined_valid
 (points:list (Ty.tySem (Ty.Prod literal_wnaf5_digit literal_wnaf5_digit)))
 (g h:list (Ty.tySem literal_wnaf_digit)):
 Forall wnaf_literal_valid g ->Forall wnaf_literal_valid h ->
 Forall secp_strauss_group_digit_valid (combine points (combine g h)).
Proof.
 intros GoodG GoodH;apply Forall_forall;intros [[d1 dl] [dg dh]] Member.
 pose proof (in_combine_r _ _ _ _ Member) as Generators.
 split.
 - apply (proj1 (Forall_forall _ _) GoodG);exact (in_combine_l _ _ _ _ Generators).
 - apply (proj1 (Forall_forall _ _) GoodH);exact (in_combine_r _ _ _ _ Generators).
Qed.
Theorem secp_literal_strauss129_group (z:Ty.tySem (Word 8))
 (table:Ty.tySem (literal_table_vector 3)) (p a:secp_group_point)
 (point:Ty.tySem literal_generator_jacobian)
 (h1 hl:Ty.tySem literal_wnaf5_digit) (t1 tl:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hg hh:Ty.tySem literal_wnaf_digit) (tg th:Ty.tySem (Vector literal_wnaf_digit 7)):
 secp_field_word z<>GZnZ.zero feP ->
 secp_table_vector_group 3 table (secp_group_odd_table p) (secp_field_word z) ->
 secp_jacobian_word_rep (secp_field_word z) point a ->
 Forall wnaf_literal_valid (hg::literal_wnaf_flatten 7 tg) ->
 Forall wnaf_literal_valid (hh::literal_wnaf_flatten 7 th) ->
 secp_jacobian_word_rep (secp_field_word z)
 (@literal_strauss_digits129 Alg.CoreFunSem
   (point,((z,table),(((h1,t1),(hl,tl)),((hg,tg),(hh,th))))))
 (fold_left (secp_strauss_group_digit_step p)
  (((h1,hl),(hg,hh))::
   combine (combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tl))
    (combine (literal_wnaf_flatten 7 tg) (literal_wnaf_flatten 7 th))) a).
Proof.
 intros Nonzero Table Start GoodG GoodH;rewrite literal_strauss_digits129_list.
 apply secp_literal_strauss_fold_group;[exact Nonzero|exact Table| |exact Start].
 constructor.
 - split;[exact (Forall_inv GoodG)|exact (Forall_inv GoodH)].
 - apply secp_strauss_combined_valid;[exact (Forall_inv_tail GoodG)|exact (Forall_inv_tail GoodH)].
Qed.

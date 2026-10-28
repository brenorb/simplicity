(** Literal off_curve_linear_combination_1 step, step2..step128 and step129,
    Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:634--660. This is the
    original routing, with four optional digits and a persistent Z/table
    context. No elliptic-curve identity replaces an off-curve operation. *)
From Coq Require Import List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_secp_generate_literal C.jet_secp_double_literal C.jet_secp_add_literal
 C.jet_secp_wnaf_literal C.jet_secp_wnaf5_literal C.jet_secp_scalar_table_literal
 C.jet_secp_lookup5_literal C.jet_secp_table_get_lambda_literal C.jet_secp_rescale_literal
 C.jet_secp_gej_negate_parametric C.jet_secp_gej_norm_literal C.jet_secp_generator_program
 C.jet_literal_division_parametric C.jet_secp_beta_spec.
Import ListNotations.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_strauss_context := Ty.Prod (Word 8) (literal_table_vector 3).
Definition literal_strauss_windows (a b:Ty.Ty) := Ty.Prod (Ty.Prod a a) (Ty.Prod b b).
Definition literal_strauss_input a b := Ty.Prod literal_generator_jacobian
 (Ty.Prod literal_strauss_context (literal_strauss_windows a b)).

Definition literal_strauss_step {term:Alg.Core.Algebra} :
 term (literal_strauss_input literal_wnaf5_digit literal_wnaf_digit) literal_generator_jacobian :=
 I (I I I H)
 &&& (I (I I O H)
  &&& (I (I O I H)
   &&& (I (I O O H) &&& O (@literal_gej_double term) &&& I O I H
      >>> Alg.Core.Combinators.case (I O H)
       ((I O H &&& (O H &&& I I H >>> @literal_lookup5 term)) >>> @literal_gej_ge_add term))
   &&& I O I H
   >>> Alg.Core.Combinators.case (I O H)
    ((I O H &&& (O H &&& I I H >>> @literal_lookup5 term >>> @literal_ge_scale_lambda term))
     >>> @literal_gej_ge_add term))
  &&& I O O H
  >>> Alg.Core.Combinators.case (I O H)
   ((I O H &&& (O (@literal_generate_small false term) &&& I I H >>> @literal_gej_zinv term))
    >>> @literal_gej_ge_add term))
 &&& I O O H
 >>> Alg.Core.Combinators.case (I O H)
  ((I O H &&& (O (@literal_generate_small true term) &&& I I H >>> @literal_gej_zinv term))
   >>> @literal_gej_ge_add term).

Fixpoint literal_strauss_block depth {term:Alg.Core.Algebra} :
 term (literal_strauss_input (Vector literal_wnaf5_digit depth) (Vector literal_wnaf_digit depth))
  literal_generator_jacobian :=
 match depth as d return
  term (literal_strauss_input (Vector literal_wnaf5_digit d) (Vector literal_wnaf_digit d))
   literal_generator_jacobian with
 | Datatypes.O=>@literal_strauss_step term
 | Datatypes.S d=>
   let rec:=@literal_strauss_block d term in
   ((O H &&& I (O H &&& I ((O O O H &&& O I O H) &&& (I O O H &&& I I O H)))) >>> rec)
   &&& I (O H &&& I ((O O I H &&& O I I H) &&& (I O I H &&& I I I H))) >>> rec
 end.

Definition literal_strauss_digits129 {term:Alg.Core.Algebra} :
 term (literal_strauss_input
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))) literal_generator_jacobian :=
 ((O H &&& I (O H &&& I ((O O O H &&& O I O H) &&& (I O O H &&& I I O H))))
  >>> @literal_strauss_step term)
 &&& I (O H &&& I ((O O I H &&& O I I H) &&& (I O I H &&& I I I H)))
 >>> @literal_strauss_block 7 term.

Local Opaque literal_gej_double literal_gej_ge_add literal_lookup5 literal_ge_scale_lambda
 literal_generate_small literal_gej_zinv.

Lemma literal_strauss_step_value (point:Ty.tySem literal_generator_jacobian)
 (z:Ty.tySem (Word 8)) (table:Ty.tySem (literal_table_vector 3))
 (d1 dlam:Ty.tySem literal_wnaf5_digit) (dg1 dg128:Ty.tySem literal_wnaf_digit) :
 @literal_strauss_step Alg.CoreFunSem (point,((z,table),((d1,dlam),(dg1,dg128))))=
 let doubled:=@literal_gej_double Alg.CoreFunSem point in
 let low:=match d1 with inl _=>doubled
  | inr word=>@literal_gej_ge_add Alg.CoreFunSem
    (doubled,@literal_lookup5 Alg.CoreFunSem (word,table)) end in
 let high:=match dlam with inl _=>low
  | inr word=>@literal_gej_ge_add Alg.CoreFunSem
    (low,@literal_ge_scale_lambda Alg.CoreFunSem (@literal_lookup5 Alg.CoreFunSem (word,table))) end in
 let gen1:=match dg1 with inl _=>high
  | inr word=>@literal_gej_ge_add Alg.CoreFunSem
    (high,@literal_gej_zinv Alg.CoreFunSem (@literal_generate_small false Alg.CoreFunSem word,z)) end in
 match dg128 with inl _=>gen1
 | inr word=>@literal_gej_ge_add Alg.CoreFunSem
   (gen1,@literal_gej_zinv Alg.CoreFunSem (@literal_generate_small true Alg.CoreFunSem word,z)) end.
Proof. destruct d1,dlam,dg1,dg128;reflexivity. Qed.

Lemma literal_strauss_block_step depth (point:Ty.tySem literal_generator_jacobian)
 (context:Ty.tySem literal_strauss_context)
 (lo1 hi1 lolam hilam:Ty.tySem (Vector literal_wnaf5_digit depth))
 (log1 hig1 log128 hig128:Ty.tySem (Vector literal_wnaf_digit depth)) :
 @literal_strauss_block (S depth) Alg.CoreFunSem
  (point,(context,(((lo1,hi1),(lolam,hilam)),((log1,hig1),(log128,hig128)))))=
 @literal_strauss_block depth Alg.CoreFunSem
  (@literal_strauss_block depth Alg.CoreFunSem
   (point,(context,((lo1,lolam),(log1,log128)))),
   (context,((hi1,hilam),(hig1,hig128)))).
Proof. reflexivity. Qed.

Lemma literal_strauss_digits129_step (point:Ty.tySem literal_generator_jacobian)
 (context:Ty.tySem literal_strauss_context)
 (h1:Ty.tySem literal_wnaf5_digit) (t1:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hlam:Ty.tySem literal_wnaf5_digit) (tlam:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hg1:Ty.tySem literal_wnaf_digit) (tg1:Ty.tySem (Vector literal_wnaf_digit 7))
 (hg128:Ty.tySem literal_wnaf_digit) (tg128:Ty.tySem (Vector literal_wnaf_digit 7)) :
 @literal_strauss_digits129 Alg.CoreFunSem
  (point,(context,(((h1,t1),(hlam,tlam)),((hg1,tg1),(hg128,tg128)))))=
 @literal_strauss_block 7 Alg.CoreFunSem
  (@literal_strauss_step Alg.CoreFunSem (point,(context,((h1,hlam),(hg1,hg128)))),
   (context,((t1,tlam),(tg1,tg128)))).
Proof. reflexivity. Qed.

Lemma strauss_wnaf5_flatten_length depth (v:Ty.tySem (Vector literal_wnaf5_digit depth)) :
 length (literal_wnaf5_flatten depth v)=Nat.pow 2 depth.
Proof.
 revert v;induction depth as [|depth IH];intro v;[reflexivity|destruct v as [lo hi]].
 cbn [literal_wnaf5_flatten Nat.pow];rewrite app_length,!IH;lia.
Qed.

Theorem literal_strauss_block_list depth (point:Ty.tySem literal_generator_jacobian)
 (context:Ty.tySem literal_strauss_context)
 (v1 vlam:Ty.tySem (Vector literal_wnaf5_digit depth))
 (vg1 vg128:Ty.tySem (Vector literal_wnaf_digit depth)) :
 @literal_strauss_block depth Alg.CoreFunSem (point,(context,((v1,vlam),(vg1,vg128))))=
 fold_left (fun (point:Ty.tySem literal_generator_jacobian)
  (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))=>
   @literal_strauss_step Alg.CoreFunSem (point,(context,ds)))
  (combine (combine (literal_wnaf5_flatten depth v1) (literal_wnaf5_flatten depth vlam))
   (combine (literal_wnaf_flatten depth vg1) (literal_wnaf_flatten depth vg128))) point.
Proof.
 revert point v1 vlam vg1 vg128;induction depth as [|depth IH];intros point v1 vlam vg1 vg128.
 - reflexivity.
 - destruct v1 as [lo1 hi1],vlam as [lolam hilam],vg1 as [log1 hig1],vg128 as [log128 hig128].
   rewrite literal_strauss_block_step,IH,IH.
   cbn [literal_wnaf5_flatten literal_wnaf_flatten].
   rewrite !generator_combine_app by
    (rewrite ?combine_length,?strauss_wnaf5_flatten_length,?literal_wnaf_flatten_length;reflexivity).
   rewrite fold_left_app;reflexivity.
Qed.

Theorem literal_strauss_digits129_list (point:Ty.tySem literal_generator_jacobian)
 (context:Ty.tySem literal_strauss_context)
 (h1:Ty.tySem literal_wnaf5_digit) (t1:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hlam:Ty.tySem literal_wnaf5_digit) (tlam:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hg1:Ty.tySem literal_wnaf_digit) (tg1:Ty.tySem (Vector literal_wnaf_digit 7))
 (hg128:Ty.tySem literal_wnaf_digit) (tg128:Ty.tySem (Vector literal_wnaf_digit 7)) :
 @literal_strauss_digits129 Alg.CoreFunSem
  (point,(context,(((h1,t1),(hlam,tlam)),((hg1,tg1),(hg128,tg128)))))=
 fold_left (fun (point:Ty.tySem literal_generator_jacobian)
  (ds:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))=>
   @literal_strauss_step Alg.CoreFunSem (point,(context,ds)))
  (((h1,hlam),(hg1,hg128))::
   combine (combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam))
    (combine (literal_wnaf_flatten 7 tg1) (literal_wnaf_flatten 7 tg128))) point.
Proof.
 rewrite literal_strauss_digits129_step;cbn [fold_left];apply literal_strauss_block_list.
Qed.

Local Ltac strauss_parametric_core :=
 lazymatch goal with
 | |- _ _ _ (@Alg.Core.Combinators.comp _ _ _ _ _ _) _ => apply Alg.comp_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.pair _ _ _ _ _ _) _ => apply Alg.pair_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.take _ _ _ _ _) _ => apply Alg.take_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.drop _ _ _ _ _) _ => apply Alg.drop_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.case _ _ _ _ _ _ _) _ => apply Alg.case_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.iden _ _) _ => apply Alg.iden_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.unit _ _) _ => apply Alg.unit_Parametric
 end.

Local Transparent literal_lookup5 literal_ge_scale_lambda.
Lemma strauss_lookup5_parametric : Alg.Core.Parametric (@literal_lookup5).
Proof.
 intros t1 t2 R;unfold literal_lookup5,literal_lookup5_pos,literal_lookup5_neg.
 repeat first [apply Bit.cond_Parametric|apply literal_ge_negate_parametric|strauss_parametric_core].
Qed.

Lemma strauss_scale_lambda_parametric : Alg.Core.Parametric (@literal_ge_scale_lambda).
Proof.
 intros t1 t2 R;unfold literal_ge_scale_lambda,literal_fe_multiply_beta,literal_fe_beta.
 repeat first [apply literal_fe_multiply_parametric|apply point_fe_normalize_parametric|
  apply Alg.scribe_Parametric|strauss_parametric_core].
Qed.

Lemma literal_strauss_step_parametric : Alg.Core.Parametric (@literal_strauss_step).
Proof.
 intros t1 t2 R;unfold literal_strauss_step.
 repeat first [apply literal_gej_double_parametric|apply literal_gej_ge_add_parametric|
  apply strauss_lookup5_parametric|apply strauss_scale_lambda_parametric|
  apply literal_generate_small_parametric|apply literal_gej_zinv_parametric|strauss_parametric_core].
Qed.

Lemma literal_strauss_block_parametric depth : Alg.Core.Parametric (@literal_strauss_block depth).
Proof.
 induction depth as [|depth IH];[exact literal_strauss_step_parametric|].
 intros t1 t2 R;cbn [literal_strauss_block].
 repeat first [apply IH|strauss_parametric_core].
Qed.

Lemma literal_strauss_digits129_parametric : Alg.Core.Parametric (@literal_strauss_digits129).
Proof.
 intros t1 t2 R;unfold literal_strauss_digits129.
 repeat first [apply literal_strauss_step_parametric|apply (literal_strauss_block_parametric 7)|strauss_parametric_core].
Qed.

(** Faithful Core port of generate's step, step2..step128 and step129
    from Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:614--627.
    Scalar splitting and wNAF generation are deliberately separate. *)
From Coq Require Import List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_secp_generate_literal C.jet_secp_double_literal C.jet_secp_add_literal
 C.jet_secp_wnaf_literal.
Import ListNotations.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_generator_step {term : Alg.Core.Algebra} :
 term (Ty.Prod literal_generator_jacobian (Ty.Prod literal_wnaf_digit literal_wnaf_digit))
   literal_generator_jacobian :=
 (I I H &&& ((I O H &&& O (@literal_gej_double term)) >>>
   Alg.Core.Combinators.case (I H)
     ((I H &&& O (@literal_generate_small false term)) >>> @literal_gej_ge_add term))) >>>
   Alg.Core.Combinators.case (I H)
     ((I H &&& O (@literal_generate_small true term)) >>> @literal_gej_ge_add term).

Fixpoint literal_generator_block depth {term : Alg.Core.Algebra} :
 term (Ty.Prod literal_generator_jacobian
   (Ty.Prod (Vector literal_wnaf_digit depth) (Vector literal_wnaf_digit depth)))
   literal_generator_jacobian :=
 match depth as d return term (Ty.Prod literal_generator_jacobian
   (Ty.Prod (Vector literal_wnaf_digit d) (Vector literal_wnaf_digit d))) literal_generator_jacobian with
 | Datatypes.O=>@literal_generator_step term
 | Datatypes.S d=>
   let rec:=@literal_generator_block d term in
   ((O H &&& (I O O H &&& I I O H)) >>> rec) &&& (I O I H &&& I I I H) >>> rec
 end.

Definition literal_generator_digits129 {term : Alg.Core.Algebra} :
 term (Ty.Prod literal_generator_jacobian
   (Ty.Prod (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))
            (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7)))) literal_generator_jacobian :=
 ((O H &&& (I O O H &&& I I O H)) >>> @literal_generator_step term) &&&
   (I O I H &&& I I I H) >>> @literal_generator_block 7 term.

Local Opaque literal_gej_double literal_gej_ge_add literal_generate_small.

Lemma literal_generator_step_value point d1 d128 :
 @literal_generator_step Alg.CoreFunSem (point,(d1,d128))=
 let doubled:=@literal_gej_double Alg.CoreFunSem point in
 let low:=match d1 with inl _=>doubled
   | inr word=>@literal_gej_ge_add Alg.CoreFunSem (doubled,@literal_generate_small false Alg.CoreFunSem word) end in
 match d128 with inl _=>low
   | inr word=>@literal_gej_ge_add Alg.CoreFunSem (low,@literal_generate_small true Alg.CoreFunSem word) end.
Proof. destruct d1 as [a|a],d128 as [b|b];reflexivity. Qed.

Lemma literal_generator_block_step depth point lo1 hi1 lo128 hi128 :
 @literal_generator_block (S depth) Alg.CoreFunSem (point,((lo1,hi1),(lo128,hi128)))=
 @literal_generator_block depth Alg.CoreFunSem
   (@literal_generator_block depth Alg.CoreFunSem (point,(lo1,lo128)),(hi1,hi128)).
Proof. reflexivity. Qed.

Lemma generator_combine_app A B (xs xs' : list A) (ys ys' : list B) :
 length xs=length ys -> combine (xs++xs') (ys++ys')=combine xs ys++combine xs' ys'.
Proof.
 revert ys;induction xs as [|x xs IH];intros [|y ys] Length;
   cbn in Length|-*;try discriminate;[reflexivity|].
 f_equal;apply IH;lia.
Qed.

Theorem literal_generator_block_list depth point v1 v128 :
 @literal_generator_block depth Alg.CoreFunSem (point,(v1,v128))=
 fold_left (fun point pair=>@literal_generator_step Alg.CoreFunSem (point,pair))
   (combine (literal_wnaf_flatten depth v1) (literal_wnaf_flatten depth v128)) point.
Proof.
 revert point v1 v128;induction depth as [|depth IH];intros point v1 v128.
 - reflexivity.
 - destruct v1 as [lo1 hi1],v128 as [lo128 hi128].
   rewrite literal_generator_block_step,IH,IH.
   cbn [literal_wnaf_flatten].
   rewrite generator_combine_app.
   + rewrite fold_left_app;reflexivity.
   + rewrite !literal_wnaf_flatten_length;reflexivity.
Qed.

Theorem literal_generator_digits129_list point head1 tail1 head128 tail128 :
 @literal_generator_digits129 Alg.CoreFunSem (point,((head1,tail1),(head128,tail128)))=
 fold_left (fun point pair=>@literal_generator_step Alg.CoreFunSem (point,pair))
   ((head1,head128)::combine (literal_wnaf_flatten 7 tail1) (literal_wnaf_flatten 7 tail128)) point.
Proof.
 change (@literal_generator_block 7 Alg.CoreFunSem
   (@literal_generator_step Alg.CoreFunSem (point,(head1,head128)),(tail1,tail128))=
   fold_left (fun point pair=>@literal_generator_step Alg.CoreFunSem (point,pair))
     (combine (literal_wnaf_flatten 7 tail1) (literal_wnaf_flatten 7 tail128))
     (@literal_generator_step Alg.CoreFunSem (point,(head1,head128)))).
 apply literal_generator_block_list.
Qed.

Local Ltac generator_parametric_core :=
 first [apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.case_Parametric|
   apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].

Lemma literal_generator_step_parametric : Alg.Core.Parametric (@literal_generator_step).
Proof.
 intros t1 t2 R;unfold literal_generator_step.
 repeat first [apply literal_gej_double_parametric|apply literal_gej_ge_add_parametric|
   apply literal_generate_small_parametric|generator_parametric_core].
Qed.

Lemma literal_generator_block_parametric depth : Alg.Core.Parametric (@literal_generator_block depth).
Proof.
 induction depth as [|depth IH];intros t1 t2 R.
 - exact (literal_generator_step_parametric t1 t2 R).
 - cbn [literal_generator_block].
   repeat first [apply IH|generator_parametric_core].
Qed.

Lemma literal_generator_digits129_parametric : Alg.Core.Parametric (@literal_generator_digits129).
Proof.
 intros t1 t2 R;unfold literal_generator_digits129.
 repeat first [apply literal_generator_step_parametric|apply (literal_generator_block_parametric 7)|
   generator_parametric_core].
Qed.

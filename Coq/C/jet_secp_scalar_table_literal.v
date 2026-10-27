(** Literal scalarTable5 routing from the fixed
    Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:769--781. The balanced
    pass1 ratio tree and pass2 traversal are retained, not replaced by group
    scalar multiplication or by a normalized-ratio specification. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_add_literal C.jet_secp_double_literal C.jet_secp_rescale_literal
 C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program C.jet_secp_negate_literal_contract.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_table_ge := Ty.Prod (Word 8) (Word 8).
Definition literal_table_gej := Ty.Prod literal_table_ge (Word 8).
Fixpoint literal_table_tree n := match n with
 | Datatypes.O=>literal_table_ge
 | Datatypes.S k=>Ty.Prod (Word 8) (Ty.Prod (literal_table_tree k) (literal_table_tree k)) end.
Fixpoint literal_table_vector n := match n with
 | Datatypes.O=>literal_table_ge
 | Datatypes.S k=>Ty.Prod (literal_table_vector k) (literal_table_vector k) end.

Definition literal_pass1_2 {term:Alg.Core.Algebra} :
 term (Ty.Prod literal_table_gej literal_table_ge)
 (Ty.Prod (literal_table_tree 1) (Ty.Prod literal_table_gej literal_table_ge)) :=
 iden &&& @literal_gej_ge_add_ex term >>>
 (I O H &&& (O O O H &&& I I O H)) &&& (I I H &&& O I H).
Definition literal_pass1_4 {term:Alg.Core.Algebra} :
 term (Ty.Prod literal_table_gej literal_table_ge)
 (Ty.Prod (literal_table_tree 2) (Ty.Prod literal_table_gej literal_table_ge)) :=
 @literal_pass1_2 term >>> O H &&& I
 (@literal_gej_ge_add_ex term &&& I H >>> O O H &&& (O I H &&& I H >>> @literal_pass1_2 term)) >>>
 (I O H &&& (O H &&& I I O H)) &&& I I I H.
Definition literal_pass1_8 {term:Alg.Core.Algebra} :
 term (Ty.Prod literal_table_gej literal_table_ge) (Ty.Prod (literal_table_tree 3) (Word 8)) :=
 @literal_pass1_4 term >>> O H &&& I
 (@literal_gej_ge_add_ex term &&& I H >>> O O H &&& (O I H &&& I H >>> @literal_pass1_4 term)) >>>
 (I O H &&& (O H &&& I I O H)) &&& I (I (I O I H)).

Definition literal_pass2_1 {term:Alg.Core.Algebra} :
 term (Ty.Prod literal_table_ge (Word 8)) literal_table_ge := O H &&& I H >>> @literal_gej_zinv term.
Definition literal_pass2_2 {term:Alg.Core.Algebra} :
 term (Ty.Prod (literal_table_tree 1) (Word 8)) (Ty.Prod (literal_table_vector 1) (Word 8)) :=
 (O I O H &&& (O O H &&& I H >>> @literal_fe_multiply term)) &&&
 (O I I H &&& I H >>> @literal_pass2_1 term) >>> (O (@literal_pass2_1 term) &&& I H) &&& O I H.
Definition literal_pass2_4 {term:Alg.Core.Algebra} :
 term (Ty.Prod (literal_table_tree 2) (Word 8)) (Ty.Prod (literal_table_vector 2) (Word 8)) :=
 (O O H &&& O I O H) &&& (O I I H &&& I H >>> @literal_pass2_2 term) >>>
 (O I H &&& (O O H &&& I I H >>> @literal_fe_multiply term) >>> @literal_pass2_2 term) &&& I O H >>>
 (O O H &&& I H) &&& O I H.
Definition literal_pass2_8 {term:Alg.Core.Algebra} :
 term (literal_table_tree 3) (literal_table_vector 3) :=
 (O H &&& I O H) &&& (I I H &&& (unit >>> @literal_fe_one256 term) >>> @literal_pass2_4 term) >>>
 (O I H &&& (O O H &&& I I H >>> @literal_fe_multiply term) >>> @literal_pass2_4 term) &&& I O H >>>
 O O H &&& I H.
Definition literal_scalar_table5 {term:Alg.Core.Algebra} :
 term literal_table_gej (Ty.Prod (Word 8) (literal_table_vector 3)) :=
 iden &&& @literal_gej_double term >>>
 I I H &&& (((O O H &&& I I H >>> @literal_gej_zinv term) &&& O I H) &&& I O H >>> @literal_pass1_8 term) >>>
 (O H &&& I I H >>> @literal_fe_multiply term) &&& I (O (@literal_pass2_8 term)).

(** These functions expose routing only: each addition is still the exact
    fixed literal extended program, retaining its raw ratio word. *)
Fixpoint literal_table_advance n (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge) :=
 match n with
 | Datatypes.O=>a
 | Datatypes.S k=>snd (@literal_gej_ge_add_ex Alg.CoreFunSem (literal_table_advance k a b,b)) end.
Definition literal_table_ratio n a b := fst (@literal_gej_ge_add_ex Alg.CoreFunSem (literal_table_advance n a b,b)).
Local Opaque literal_gej_ge_add_ex literal_gej_double literal_gej_zinv literal_fe_multiply literal_fe_one256.

Lemma literal_pass1_2_step a b : @literal_pass1_2 Alg.CoreFunSem (a,b)=
 ((literal_table_ratio 0 a b,(fst a,fst (literal_table_advance 1 a b))),
  (literal_table_advance 1 a b,b)).
Proof. destruct a as [[x y] z];destruct b as [u v];reflexivity. Qed.
Lemma literal_pass1_4_step a b : @literal_pass1_4 Alg.CoreFunSem (a,b)=
 ((literal_table_ratio 1 a b,
   ((literal_table_ratio 0 a b,(fst a,fst (literal_table_advance 1 a b))),
    (literal_table_ratio 2 a b,(fst (literal_table_advance 2 a b),fst (literal_table_advance 3 a b))))),
  (literal_table_advance 3 a b,b)).
Proof. destruct a as [[x y] z];destruct b as [u v];reflexivity. Qed.
Theorem literal_pass1_8_step a b : @literal_pass1_8 Alg.CoreFunSem (a,b)=
 ((literal_table_ratio 3 a b,
   ((literal_table_ratio 1 a b,
     ((literal_table_ratio 0 a b,(fst a,fst (literal_table_advance 1 a b))),
      (literal_table_ratio 2 a b,(fst (literal_table_advance 2 a b),fst (literal_table_advance 3 a b))))),
    (literal_table_ratio 5 a b,
     ((literal_table_ratio 4 a b,(fst (literal_table_advance 4 a b),fst (literal_table_advance 5 a b))),
      (literal_table_ratio 6 a b,(fst (literal_table_advance 6 a b),fst (literal_table_advance 7 a b))))))),
  snd (literal_table_advance 7 a b)).
Proof. destruct a as [[x y] z];destruct b as [u v];reflexivity. Qed.

Lemma literal_pass1_2_parametric : Alg.Core.Parametric (@literal_pass1_2).
Proof.
 intros term1 term2 R;unfold literal_pass1_2.
 repeat first [apply literal_gej_ge_add_ex_parametric|apply Alg.comp_Parametric|apply Alg.pair_Parametric|
  apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.
Lemma literal_pass1_4_parametric : Alg.Core.Parametric (@literal_pass1_4).
Proof.
 intros term1 term2 R;unfold literal_pass1_4.
 repeat first [apply literal_pass1_2_parametric|apply literal_gej_ge_add_ex_parametric|apply Alg.comp_Parametric|
  apply Alg.pair_Parametric|apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.
Lemma literal_pass1_8_parametric : Alg.Core.Parametric (@literal_pass1_8).
Proof.
 intros term1 term2 R;unfold literal_pass1_8.
 repeat first [apply literal_pass1_4_parametric|apply literal_gej_ge_add_ex_parametric|apply Alg.comp_Parametric|
  apply Alg.pair_Parametric|apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.

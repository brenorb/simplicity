(** Exact field square-root program port; not yet a C jet equivalence proof. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_square_execution C.jet_secp_rescale_literal C.jet_secp_curve_literal
 C.jet_secp_negate_literal_contract C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program
 C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate C.jet_literal_division_parametric.
Local Open Scope term_scope.
Set Default Timeout 10.

(** Positive counts have the same right association as Haskell foldr1 (>>>).
    The zero case is an internal identity and is not used by the tower. *)
Fixpoint literal_fe_squares (n : nat) {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
 match n with
 | Datatypes.O => iden
 | S k => match k with
   | Datatypes.O => @literal_fe_square term
   | S _ => @literal_fe_square term >>> @literal_fe_squares k term
   end
 end.
Definition literal_fe_tower {term : Alg.Core.Algebra} : term (Word 8) (Ty.Prod (Word 8) (Word 8)) :=
iden &&& (@literal_fe_cube term)
        >>> I H &&& (O H &&& I (@literal_fe_square term) >>> (@literal_fe_multiply term))
        >>> O H &&& ((I H &&& (O H &&& (I (iden &&& (iden &&& ((@literal_fe_square term) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term) >>> (@literal_fe_square term) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)
                          >>> iden &&& (@literal_fe_squares 11 term) >>> (@literal_fe_multiply term)))
                 >>> I H &&& (O H &&& I (iden &&& (@literal_fe_squares 22 term) >>> (@literal_fe_multiply term)
                                     >>> (iden &&& (iden &&& (@literal_fe_squares 44 term) >>> (@literal_fe_multiply term)
                                                 >>> iden &&& (@literal_fe_squares 88 term) >>> (@literal_fe_multiply term)
                                           >>> (@literal_fe_squares 44 term)) >>> (@literal_fe_multiply term))
                                    >>> (@literal_fe_square term) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)
                           >>> (@literal_fe_squares 23 term)) >>> (@literal_fe_multiply term)
                 >>> (@literal_fe_squares 5 term)).
Definition literal_fe_square_root {term : Alg.Core.Algebra} : term (Word 8) (Ty.Sum Ty.Unit (Word 8)) :=
 iden &&& @literal_fe_tower term
 >>> O H &&& I ((O H &&& I (@literal_fe_square term) >>> @literal_fe_multiply term)
               >>> @literal_fe_square term >>> @literal_fe_square term)
 >>> (O (@literal_fe_negate term) &&& I (@literal_fe_square term) >>> @literal_fe_add term
      >>> @canonical_fe_is_zero term) &&& I H
 >>> Bit.cond (injr iden) (injl unit).

Local Opaque literal_fe_square literal_fe_cube literal_fe_multiply literal_fe_negate
 literal_fe_add canonical_fe_is_zero.

Lemma literal_fe_squares_comp n {term : Alg.Core.Algebra} :
 @literal_fe_squares (S (S n)) term=
 (@literal_fe_square term >>> @literal_fe_squares (S n) term).
Proof. reflexivity. Qed.

Lemma literal_fe_squares_parametric n : Alg.Core.Parametric (@literal_fe_squares n).
Proof.
 induction n as [|n IH];intros term1 term2 R.
 - apply Alg.iden_Parametric.
 - destruct n as [|n].
   + apply curve_square_parametric.
   + apply Alg.comp_Parametric;[apply curve_square_parametric|apply IH].
Qed.
Lemma literal_fe_tower_parametric : Alg.Core.Parametric (@literal_fe_tower).
Proof.
 intros term1 term2 R;unfold literal_fe_tower.
 repeat first [apply literal_fe_squares_parametric | apply curve_square_parametric |
   apply curve_cube_parametric | apply literal_fe_multiply_parametric |
   apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
   apply Alg.drop_Parametric | apply Alg.iden_Parametric].
Qed.
Lemma literal_fe_square_root_parametric : Alg.Core.Parametric (@literal_fe_square_root).
Proof.
 intros term1 term2 R;unfold literal_fe_square_root.
 repeat first [apply literal_fe_tower_parametric | apply curve_square_parametric | apply literal_fe_multiply_parametric |
   apply literal_fe_negate_parametric | apply literal_fe_add_parametric |
   apply canonical_fe_is_zero_parametric | apply Bit.cond_Parametric |
   apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
   apply Alg.drop_Parametric | apply Alg.injr_Parametric | apply Alg.injl_Parametric |
   apply Alg.unit_Parametric | apply Alg.iden_Parametric].
Qed.

Local Opaque literal_fe_tower.
Lemma literal_fe_square_root_step (x : Ty.tySem (Word 8)) :
 let t := @literal_fe_tower Alg.CoreFunSem x in
 let r := @literal_fe_square Alg.CoreFunSem
   (@literal_fe_square Alg.CoreFunSem
     (@literal_fe_multiply Alg.CoreFunSem (fst t,@literal_fe_square Alg.CoreFunSem (snd t)))) in
 @literal_fe_square_root Alg.CoreFunSem x=
 match @canonical_fe_is_zero Alg.CoreFunSem
  (@literal_fe_add Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem x,@literal_fe_square Alg.CoreFunSem r)) with
 | inl _ => inl tt
 | inr _ => inr r
 end.
Proof. reflexivity. Qed.

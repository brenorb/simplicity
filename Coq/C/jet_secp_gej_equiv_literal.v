(** Exact gej_equiv composition in the fixed LibSecp256k1 program. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_gej_negate_literal C.jet_secp_gej_negate_parametric
 C.jet_secp_add_literal C.jet_secp_literal_gej_predicate.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_gej_equiv {term : Alg.Core.Algebra} :
 term (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
              (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
      (Ty.Sum Ty.Unit Ty.Unit) :=
 O (@literal_gej_negate term) &&& I H >>> @literal_gej_add term >>> @literal_gej_is_infinity term.

Lemma literal_gej_equiv_parametric : Alg.Core.Parametric (@literal_gej_equiv).
Proof.
 intros term1 term2 R;unfold literal_gej_equiv.
 repeat first [apply literal_gej_negate_parametric | apply literal_gej_add_parametric |
  apply literal_gej_is_infinity_parametric | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
  apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric].
Qed.

Lemma literal_gej_equiv_step
 (a b : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) :
 @literal_gej_equiv Alg.CoreFunSem (a,b)=
 @literal_gej_is_infinity Alg.CoreFunSem
  (@literal_gej_add Alg.CoreFunSem (@literal_gej_negate Alg.CoreFunSem a,b)).
Proof. reflexivity. Qed.

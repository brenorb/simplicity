(** Literal addition trees from the fixed LibSecp256k1 program. These are
    specification ports for actual C mixed-addition proofs, not jet endpoints. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
  C.jet_secp_negate_literal_contract C.jet_secp_square_execution C.jet_secp_multiply_literal_spec
  C.jet_secp_literal_add_program C.jet_secp_literal_infinity C.jet_secp_literal_gej_predicate
  C.jet_secp_rescale_literal C.jet_secp_double_literal C.jet_secp_curve_literal
  C.jet_secp_gej_negate_parametric C.jet_literal_division_parametric.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_gej_add_ex {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
                (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
       (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) :=
  let zeroH := O (O (@canonical_fe_is_zero term)) &&& I O H >>> Bit.cond (O I H &&& (@literal_gej_double term)) (unit >>> (@literal_fe_zero256 term) &&& (@literal_gej_infinity term)) in
  let nonZeroH := (O O H &&& ((O O H &&& I I O I H >>> (@literal_fe_multiply term)) &&& I I I H)) &&& ((O (O (@literal_fe_square term)) &&& O I H >>> (@literal_fe_multiply term)) &&& I O H)
             >>> ((O O H &&& O I I H >>> (@literal_fe_multiply term)) &&& O (I (@literal_fe_multiply term))) &&& (((O O H >>> (@literal_fe_cube term)) &&& I O H) &&& I I H)
             >>> O O H &&& I ((((O (O H &&& I ((@literal_fe_multiply_int (-2) term)) >>> (@literal_fe_add term)) &&& I (O (@literal_fe_square term)) >>> (@literal_fe_add term)) &&& O I H) &&& (I O H &&& (O O H &&& I I H >>> (@literal_fe_multiply term))))
                          >>> O O H &&& (I I H &&& (I O H &&& O (O H &&& I (@literal_fe_negate term) >>> (@literal_fe_add term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_add term)))
                     &&& O I H in
  let body := ((O O O H &&& (I I H >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)) &&& (I (O (O (@literal_fe_negate term))) &&& (O I H >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_add term) &&& O H)
         &&& ((O O I H  &&& (I I H >>> (@literal_fe_cube term)) >>> (@literal_fe_multiply term))   &&& (I (O (I (@literal_fe_negate term))) &&& (O I H >>> (@literal_fe_cube term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_add term) &&& O H) &&&
             (O H &&& I (I (@literal_fe_negate term)))
         >>> O (O (@canonical_fe_is_zero term)) &&& iden >>> Bit.cond (I zeroH) nonZeroH in
  O (@literal_gej_is_infinity term) &&& iden
  >>> Bit.cond ((unit >>> (@literal_fe_zero256 term)) &&& (I (O (O (@canonical_fe_normalize term) &&& I (@canonical_fe_normalize term)) &&& (I (@canonical_fe_normalize term)))))
           (I (@literal_gej_is_infinity term) &&& iden
        >>> Bit.cond ((unit >>> (@literal_fe_one256 term)) &&& (O (O (O (@canonical_fe_normalize term) &&& I (@canonical_fe_normalize term)) &&& (I (@canonical_fe_normalize term))))) body).

Definition literal_gej_add {term : Alg.Core.Algebra} := @literal_gej_add_ex term >>> I H.
Definition literal_gej_ge_add_ex {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8)))
       (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) :=
  O H &&& (I H &&& (unit >>> @literal_fe_one256 term)) >>> @literal_gej_add_ex term.
Definition literal_gej_ge_add {term : Alg.Core.Algebra} := @literal_gej_ge_add_ex term >>> I H.

Lemma literal_gej_add_ex_parametric : Alg.Core.Parametric (@literal_gej_add_ex).
Proof.
  intros term1 term2 R;unfold literal_gej_add_ex.
  repeat first [apply literal_gej_double_parametric | apply literal_gej_infinity_parametric |
    apply literal_gej_is_infinity_parametric | apply point_fe_normalize_parametric |
    apply canonical_fe_is_zero_parametric | apply literal_fe_multiply_int_parametric |
    apply curve_square_parametric | apply curve_cube_parametric |
    apply literal_fe_add_parametric | apply literal_fe_multiply_parametric |
    apply literal_fe_negate_parametric | apply literal_fe_one256_parametric |
    apply literal_fe_zero256_parametric | apply Bit.cond_Parametric |
    apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
    apply Alg.drop_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.
Lemma literal_gej_add_parametric : Alg.Core.Parametric (@literal_gej_add).
Proof.
  intros term1 term2 R;unfold literal_gej_add.
  apply Alg.comp_Parametric;[apply literal_gej_add_ex_parametric|apply Alg.drop_Parametric;apply Alg.iden_Parametric].
Qed.
Lemma literal_gej_ge_add_ex_parametric : Alg.Core.Parametric (@literal_gej_ge_add_ex).
Proof.
  intros term1 term2 R;unfold literal_gej_ge_add_ex.
  repeat first [apply literal_gej_add_ex_parametric | apply literal_fe_one256_parametric |
    apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
    apply Alg.drop_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.
Lemma literal_gej_ge_add_parametric : Alg.Core.Parametric (@literal_gej_ge_add).
Proof.
  intros term1 term2 R;unfold literal_gej_ge_add.
  apply Alg.comp_Parametric;[apply literal_gej_ge_add_ex_parametric|apply Alg.drop_Parametric;apply Alg.iden_Parametric].
Qed.

Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
  literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
  literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity.

Lemma literal_gej_add_ex_infinite (ax ay az bx byword bz : Ty.tySem (Word 8)) :
  @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt ->
  @literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))=
    (@literal_fe_zero256 Alg.CoreFunSem tt,
      ((@canonical_fe_normalize Alg.CoreFunSem bx,@canonical_fe_normalize Alg.CoreFunSem byword),
       @canonical_fe_normalize Alg.CoreFunSem bz)).
Proof.
  intro HInf;unfold literal_gej_add_ex.
  cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
    literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
    literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity].
  match goal with
  | |- (match ?c with inl _ => _ | inr _ => _ end) = _ =>
    assert (HInf' : c=inr tt) by exact HInf;rewrite HInf';reflexivity
  end.
Qed.
Lemma literal_gej_ge_add_expansion
    (a : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
    (b : Ty.tySem (Ty.Prod (Word 8) (Word 8))) :
  @literal_gej_ge_add Alg.CoreFunSem (a,b)=
  snd (@literal_gej_add_ex Alg.CoreFunSem (a,(b,@literal_fe_one256 Alg.CoreFunSem tt))).
Proof. reflexivity. Qed.
Lemma literal_gej_ge_add_infinite (ax ay az bx byword : Ty.tySem (Word 8)) :
  @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt ->
  @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword))=
    ((@canonical_fe_normalize Alg.CoreFunSem bx,@canonical_fe_normalize Alg.CoreFunSem byword),
      @canonical_fe_normalize Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)).
Proof.
  intro HInf;rewrite literal_gej_ge_add_expansion,literal_gej_add_ex_infinite by exact HInf.
  reflexivity.
Qed.

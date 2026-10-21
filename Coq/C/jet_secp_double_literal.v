(** Literal Core routing of LibSecp256k1.gej_double and its fe_halve helper.
    These are the fixed target's ports, not a replacement numeric specification. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_literal_add_program
  C.jet_secp_negate_literal_contract C.jet_secp_square_execution
  C.jet_secp_multiply_literal_spec C.jet_secp_curve_literal
  C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity C.jet_literal_division_parametric.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition double_half_word : Ty.tySem (Word 8) := @fromZ (WordToZ 8) ((feP+1)/2).
Definition double_multiplier_word i : Ty.tySem (Word 8) := @fromZ (WordToZ 8) (i mod feP).
Definition literal_fe_multiply_int i {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  Alg.scribe (double_multiplier_word i) &&& iden >>> @literal_fe_multiply term.

(** LibSecp256k1.hs:490. full_shift word1 word256 is the rightward one-bit
    tuple shift; the following pair swaps its word and bit results. *)
Definition literal_fe_halve {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  (Bit.false &&& iden) >>> @Word.full_right_shift1 Bit 8 term >>> I H &&& O H >>>
    Bit.cond ((unit >>> Alg.scribe double_half_word) &&& iden >>> @literal_fe_add term) iden.

(** LibSecp256k1.hs:512-522, preserving the canonical pairing/projection tree. *)
Definition literal_gej_double_body {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
    (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) :=
  (O (O H &&& ((O (@literal_fe_square term) >>> @literal_fe_multiply_int 3 term >>> @literal_fe_halve term)
      &&& I (@literal_fe_square term)))
    >>> ((I (I H) &&& O H >>> @literal_fe_multiply term >>> @literal_fe_negate term) &&& I H)
    >>> (((O (@literal_fe_multiply_int 2 term) &&& I (O (@literal_fe_square term))
      >>> @literal_fe_add term) &&& O H) &&& I H)
    >>> (O (O H) &&& ((I (O H) &&& O (@literal_fe_add term) >>> @literal_fe_multiply term)
      &&& I (I (@literal_fe_square term)) >>> @literal_fe_add term >>> @literal_fe_negate term)))
    &&& (O (I H) &&& I H >>> @literal_fe_multiply term).
Definition literal_gej_double {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
    (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) :=
  @literal_gej_is_infinity term &&& iden >>>
    Bit.cond (unit >>> @literal_gej_infinity term) (@literal_gej_double_body term).

Lemma literal_fe_multiply_int_parametric i : Alg.Core.Parametric (@literal_fe_multiply_int i).
Proof.
  intros term1 term2 R;unfold literal_fe_multiply_int.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.scribe_Parametric | apply Alg.iden_Parametric].
  - apply literal_fe_multiply_parametric.
Qed.
Lemma literal_fe_halve_parametric : Alg.Core.Parametric (@literal_fe_halve).
Proof.
  intros term1 term2 R;unfold literal_fe_halve.
  repeat first [apply literal_fe_add_parametric | apply Word.full_right_shift1_Parametric |
    apply Bit.false_Parametric | apply Bit.cond_Parametric | apply Alg.scribe_Parametric |
    apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
    apply Alg.drop_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.
Lemma literal_gej_double_body_parametric : Alg.Core.Parametric (@literal_gej_double_body).
Proof.
  intros term1 term2 R;unfold literal_gej_double_body.
  repeat first [apply literal_fe_multiply_int_parametric | apply literal_fe_halve_parametric |
    apply curve_square_parametric | apply literal_fe_add_parametric |
    apply literal_fe_multiply_parametric | apply literal_fe_negate_parametric |
    apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
    apply Alg.drop_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.
Lemma literal_gej_double_parametric : Alg.Core.Parametric (@literal_gej_double).
Proof.
  intros term1 term2 R;unfold literal_gej_double.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric;[apply literal_gej_is_infinity_parametric|apply Alg.iden_Parametric].
  - apply Bit.cond_Parametric;
    [apply Alg.comp_Parametric;[apply Alg.unit_Parametric|apply literal_gej_infinity_parametric]
    |apply literal_gej_double_body_parametric].
Qed.

Local Opaque literal_fe_square literal_fe_multiply_int literal_fe_halve literal_fe_add
  literal_fe_multiply literal_fe_negate literal_gej_is_infinity literal_gej_infinity.

Lemma literal_gej_double_body_step (x y z : Ty.tySem (Word 8)) :
  let s := @literal_fe_square Alg.CoreFunSem y in
  let l := @literal_fe_halve Alg.CoreFunSem
    (@literal_fe_multiply_int 3 Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem x)) in
  let t := @literal_fe_negate Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (s,x)) in
  let rx := @literal_fe_add Alg.CoreFunSem
    (@literal_fe_multiply_int 2 Alg.CoreFunSem t,@literal_fe_square Alg.CoreFunSem l) in
  @literal_gej_double_body Alg.CoreFunSem ((x,y),z)=
  ((rx,@literal_fe_negate Alg.CoreFunSem
    (@literal_fe_add Alg.CoreFunSem
      (@literal_fe_multiply Alg.CoreFunSem (l,@literal_fe_add Alg.CoreFunSem (rx,t)),
       @literal_fe_square Alg.CoreFunSem s))),@literal_fe_multiply Alg.CoreFunSem (y,z)).
Proof. reflexivity. Qed.

Lemma literal_gej_double_step (x y z : Ty.tySem (Word 8)) :
  @literal_gej_double Alg.CoreFunSem ((x,y),z)=
    if Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem ((x,y),z))
    then @literal_gej_infinity Alg.CoreFunSem tt
    else @literal_gej_double_body Alg.CoreFunSem ((x,y),z).
Proof.
  change ((match @literal_gej_is_infinity Alg.CoreFunSem ((x,y),z) with
    | inl _ => @literal_gej_double_body Alg.CoreFunSem ((x,y),z)
    | inr _ => @literal_gej_infinity Alg.CoreFunSem tt
    end)=if Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem ((x,y),z))
      then @literal_gej_infinity Alg.CoreFunSem tt
      else @literal_gej_double_body Alg.CoreFunSem ((x,y),z)).
  destruct (@literal_gej_is_infinity Alg.CoreFunSem ((x,y),z)) as [u | u]; destruct u; reflexivity.
Qed.

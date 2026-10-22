(** Exact canonical decompression composition, for the original C jet proof.
    This specification port alone does not establish public jet equivalence. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_root_literal C.jet_secp_curve_literal C.jet_secp_rescale_literal
 C.jet_secp_canonical_normalize C.jet_secp_canonical_odd C.jet_secp_negate_literal_contract
 C.jet_secp_literal_add_program C.jet_literal_division_parametric C.jet_secp_gej_negate_parametric.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_y_from_x {term : Alg.Core.Algebra} :
 term (Word 8) (Ty.Sum Ty.Unit (Word 8)) :=
 ((unit >>> Alg.scribe curve_seven_word) &&& @literal_fe_cube term)
 >>> @literal_fe_add term >>> @literal_fe_square_root term.

(** Simplicity.Programs.Bit.xor s t = s &&& iden >>> cond (not t) t. *)
Definition literal_decompress_flip {term : Alg.Core.Algebra} :
 term (Ty.Prod (Word 8) (Ty.Prod Bit (Word 8))) Bit :=
 (O (@canonical_fe_is_odd term) &&& iden)
 >>> Bit.cond (Bit.not (I (O H))) (I (O H)).
Definition literal_decompress_point {term : Alg.Core.Algebra} :
 term (Ty.Prod (Word 8) (Ty.Prod Bit (Word 8))) (Ty.Prod (Word 8) (Word 8)) :=
 I (I (@canonical_fe_normalize term)) &&&
 ((@literal_decompress_flip term &&& O H) >>> Bit.cond (@literal_fe_negate term) iden).
Definition literal_decompress {term : Alg.Core.Algebra} :
 term (Ty.Prod Bit (Word 8)) (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 8))) :=
 I (@literal_y_from_x term) &&& iden >>> case (injl unit) (injr (@literal_decompress_point term)).

Lemma decompress_odd_parametric : Alg.Core.Parametric (@canonical_fe_is_odd).
Proof.
 intros term1 term2 R;unfold canonical_fe_is_odd.
 apply Alg.comp_Parametric;[apply point_fe_normalize_parametric|apply Word.rightmost_Parametric].
Qed.
Lemma literal_y_from_x_parametric : Alg.Core.Parametric (@literal_y_from_x).
Proof.
 intros term1 term2 R;unfold literal_y_from_x.
 apply Alg.comp_Parametric.
 - apply Alg.pair_Parametric.
   + apply Alg.comp_Parametric;[apply Alg.unit_Parametric|apply Alg.scribe_Parametric].
   + apply curve_cube_parametric.
 - apply Alg.comp_Parametric;[apply literal_fe_add_parametric|apply literal_fe_square_root_parametric].
Qed.
Lemma literal_decompress_flip_parametric : Alg.Core.Parametric (@literal_decompress_flip).
Proof.
 intros term1 term2 R;unfold literal_decompress_flip.
 repeat first [apply decompress_odd_parametric | apply Bit.not_Parametric | apply Bit.cond_Parametric |
  apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric |
  apply Alg.drop_Parametric | apply Alg.iden_Parametric].
Qed.
Lemma literal_decompress_point_parametric : Alg.Core.Parametric (@literal_decompress_point).
Proof.
 intros term1 term2 R;unfold literal_decompress_point.
 repeat first [apply literal_decompress_flip_parametric | apply point_fe_normalize_parametric |
  apply literal_fe_negate_parametric | apply Bit.cond_Parametric | apply Alg.comp_Parametric |
  apply Alg.pair_Parametric | apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric].
Qed.
Lemma literal_decompress_parametric : Alg.Core.Parametric (@literal_decompress).
Proof.
 intros term1 term2 R;unfold literal_decompress.
 repeat first [apply literal_y_from_x_parametric | apply literal_decompress_point_parametric |
  apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.drop_Parametric |
  apply Alg.case_Parametric | apply Alg.injl_Parametric | apply Alg.injr_Parametric |
  apply Alg.unit_Parametric | apply Alg.iden_Parametric].
Qed.

Local Opaque literal_fe_cube literal_fe_add literal_fe_square_root canonical_fe_normalize
 canonical_fe_is_odd literal_fe_negate.
Lemma literal_y_from_x_step (x : Ty.tySem (Word 8)) :
 @literal_y_from_x Alg.CoreFunSem x=
 @literal_fe_square_root Alg.CoreFunSem
  (@literal_fe_add Alg.CoreFunSem (curve_seven_word,@literal_fe_cube Alg.CoreFunSem x)).
Proof.
 unfold literal_y_from_x;cbn -[Alg.scribe literal_fe_cube literal_fe_add literal_fe_square_root].
 rewrite Alg.scribe_correct;reflexivity.
Qed.

Lemma literal_decompress_flip_value (y x : Ty.tySem (Word 8)) (odd : Ty.tySem Bit) :
 Bit.toBool (@literal_decompress_flip Alg.CoreFunSem (y,(odd,x)))=
 xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) (Bit.toBool odd).
Proof.
 unfold literal_decompress_flip.
 change (Bit.toBool (match @canonical_fe_is_odd Alg.CoreFunSem y with
  | inl _ => odd | inr _ => match odd with inl _ => inr tt | inr _ => inl tt end end)=
  xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) (Bit.toBool odd)).
 destruct (@canonical_fe_is_odd Alg.CoreFunSem y) as [b|b];
  destruct b;destruct odd as [b|b];destruct b;reflexivity.
Qed.

Lemma literal_decompress_point_step (y x : Ty.tySem (Word 8)) (odd : Ty.tySem Bit) :
 @literal_decompress_point Alg.CoreFunSem (y,(odd,x))=
 (@canonical_fe_normalize Alg.CoreFunSem x,
   if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) (Bit.toBool odd)
   then @literal_fe_negate Alg.CoreFunSem y else y).
Proof.
 unfold literal_decompress_point.
 change ((@canonical_fe_normalize Alg.CoreFunSem x,
  match @literal_decompress_flip Alg.CoreFunSem (y,(odd,x)) with
  | inl _ => y | inr _ => @literal_fe_negate Alg.CoreFunSem y end)=
  (@canonical_fe_normalize Alg.CoreFunSem x,
   if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) (Bit.toBool odd)
   then @literal_fe_negate Alg.CoreFunSem y else y)).
 rewrite <-(literal_decompress_flip_value y x odd).
 destruct (@literal_decompress_flip Alg.CoreFunSem (y,(odd,x))) as [b|b];destruct b;reflexivity.
Qed.

Lemma literal_decompress_step (x : Ty.tySem (Word 8)) (odd : Ty.tySem Bit) :
 @literal_decompress Alg.CoreFunSem (odd,x)=
 match @literal_y_from_x Alg.CoreFunSem x with
 | inl _ => inl tt
 | inr y => inr (@canonical_fe_normalize Alg.CoreFunSem x,
    if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) (Bit.toBool odd)
    then @literal_fe_negate Alg.CoreFunSem y else y)
 end.
Proof.
 unfold literal_decompress.
 change ((match @literal_y_from_x Alg.CoreFunSem x with
  | inl _ => inl tt | inr y => inr (@literal_decompress_point Alg.CoreFunSem (y,(odd,x))) end)=
  match @literal_y_from_x Alg.CoreFunSem x with
  | inl _ => inl tt
  | inr y => inr (@canonical_fe_normalize Alg.CoreFunSem x,
    if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) (Bit.toBool odd)
    then @literal_fe_negate Alg.CoreFunSem y else y)
  end).
 destruct (@literal_y_from_x Alg.CoreFunSem x) as [b|y];[destruct b;reflexivity|].
 rewrite literal_decompress_point_step;reflexivity.
Qed.

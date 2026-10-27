(** Faithful full scalar_split_lambda port from the frozen
    Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:593--606. The original
    multiply/round/subtract routing, signed extension, lambda computation,
    msb selection and both signed-half outputs are retained. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_multiply_spec C.jet_subtract_spec C.jet_canonical_add_adapter
 C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_negate C.jet_secp_canonical_scalar_negate_parametric
 C.jet_secp_canonical_scalar_add C.jet_secp_canonical_scalar_lambda C.jet_secp_scalar_canonical_parametric
 C.jet_secp_split_round_literal C.jet_secp_split_constants C.jet_secp_split_signed_bounds.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_split_half := Ty.Prod Bit (Word 7).
Definition literal_split_basis_value (first:bool) := if first then split_basis_value Datatypes.true else split_lattice_b2.
Definition literal_split_basis_word first := @fromZ (WordToZ 7) (literal_split_basis_value first).
Definition literal_split_high {term:Alg.Core.Algebra} : term Ty.Unit (Word 7) :=
 @Word.fill Ty.Unit Bit 7 term (@Bit.true Ty.Unit term).
Definition literal_split_product (first:bool) {term:Alg.Core.Algebra} : term (Word 8) (Word 8) :=
 (@literal_split_coefficient first term &&& (unit >>> Alg.scribe (literal_split_basis_word first))) >>>
 @multiply_word_spec 7 term.
Definition literal_split_second {term:Alg.Core.Algebra} : term (Word 8) literal_split_half :=
 (@literal_split_product Datatypes.true term &&& @literal_split_product Datatypes.false term) >>>
 @subtract_word_spec term 8 >>> O H &&& I I H.
Definition literal_split_signed_scalar {term:Alg.Core.Algebra} : term literal_split_half (Word 8) :=
 Bit.cond
  ((((unit >>> @literal_split_high term) &&& iden) &&& (unit >>> Alg.scribe canonical_group_word)) >>>
   @canonical_add_word 8 term >>> I H)
  ((unit >>> @Word.zero 7 term) &&& iden).
Definition literal_split_pack_half {term:Alg.Core.Algebra} : term (Word 8) literal_split_half :=
 (@Word.leftmost Bit 8 term &&& iden) >>> Bit.cond
  ((iden &&& (unit >>> Alg.scribe canonical_group_word)) >>> @subtract_word_spec term 8 >>> injr unit &&& I I H)
  (injl unit &&& I H).
Definition literal_split_first {term:Alg.Core.Algebra} :
 term (Ty.Prod (Word 8) literal_split_half) literal_split_half :=
 (O H &&& I (((@literal_split_signed_scalar term &&& (unit >>> @canonical_scalar_lambda term)) >>>
  @canonical_scalar_multiply term) >>> @canonical_scalar_negate term)) >>>
 @canonical_scalar_add term >>> @literal_split_pack_half term.
Definition literal_scalar_split_lambda {term:Alg.Core.Algebra} :
 term (Word 8) (Ty.Prod literal_split_half literal_split_half) :=
 @canonical_scalar_normalize term >>> (iden &&& @literal_split_second term) >>>
 @literal_split_first term &&& I H.

Local Ltac split_parametric_core := lazymatch goal with
 | |- _ _ _ (@Alg.Core.Combinators.comp _ _ _ _ _ _) _ => apply Alg.comp_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.pair _ _ _ _ _ _) _ => apply Alg.pair_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.take _ _ _ _ _) _ => apply Alg.take_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.drop _ _ _ _ _) _ => apply Alg.drop_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.injl _ _ _ _ _) _ => apply Alg.injl_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.injr _ _ _ _ _) _ => apply Alg.injr_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.iden _ _) _ => apply Alg.iden_Parametric
 | |- _ _ _ (@Alg.Core.Combinators.unit _ _) _ => apply Alg.unit_Parametric
 end.

Lemma literal_split_high_parametric : Alg.Core.Parametric (@literal_split_high).
Proof. intros a b R;unfold literal_split_high;apply Word.fill_Parametric;apply Bit.true_Parametric. Qed.
Lemma literal_split_product_parametric first : Alg.Core.Parametric (@literal_split_product first).
Proof.
 intros a b R;unfold literal_split_product.
 repeat first [exact (literal_split_coefficient_parametric first a b R)|
  apply multiply_word_spec_parametric|apply Alg.scribe_Parametric|split_parametric_core].
Qed.
Lemma literal_split_second_parametric : Alg.Core.Parametric (@literal_split_second).
Proof.
 intros a b R;unfold literal_split_second.
 repeat first [exact (literal_split_product_parametric Datatypes.true a b R)|
  exact (literal_split_product_parametric Datatypes.false a b R)|apply subtract_word_spec_parametric|split_parametric_core].
Qed.
Lemma literal_split_signed_scalar_parametric : Alg.Core.Parametric (@literal_split_signed_scalar).
Proof.
 intros a b R;unfold literal_split_signed_scalar;apply Bit.cond_Parametric.
 - repeat first [exact (literal_split_high_parametric a b R)|
   apply Alg.scribe_Parametric|apply canonical_add_word_parametric|split_parametric_core].
 - repeat first [apply Word.zero_Parametric|split_parametric_core].
Qed.
Lemma literal_split_pack_half_parametric : Alg.Core.Parametric (@literal_split_pack_half).
Proof.
 intros a b R;unfold literal_split_pack_half;apply Alg.comp_Parametric.
 - apply Alg.pair_Parametric;[apply Word.leftmost_Parametric|apply Alg.iden_Parametric].
 - apply Bit.cond_Parametric;
   repeat first [apply Alg.scribe_Parametric|apply subtract_word_spec_parametric|split_parametric_core].
Qed.
Lemma literal_split_first_parametric : Alg.Core.Parametric (@literal_split_first).
Proof.
 intros a b R;unfold literal_split_first.
 repeat first [exact (literal_split_signed_scalar_parametric a b R)|
  apply canonical_scalar_lambda_parametric|apply canonical_scalar_multiply_parametric|
  apply canonical_scalar_negate_parametric|apply canonical_scalar_add_parametric|
  exact (literal_split_pack_half_parametric a b R)|split_parametric_core].
Qed.
Lemma literal_scalar_split_lambda_parametric : Alg.Core.Parametric (@literal_scalar_split_lambda).
Proof.
 intros a b R;unfold literal_scalar_split_lambda.
 repeat first [apply canonical_scalar_normalize_parametric|exact (literal_split_second_parametric a b R)|
  exact (literal_split_first_parametric a b R)|split_parametric_core].
Qed.

Local Opaque canonical_scalar_normalize literal_split_second literal_split_first.
Lemma literal_scalar_split_lambda_step k : @literal_scalar_split_lambda Alg.CoreFunSem k=
 let normalized:=@canonical_scalar_normalize Alg.CoreFunSem k in
 let second:=@literal_split_second Alg.CoreFunSem normalized in
 (@literal_split_first Alg.CoreFunSem (normalized,second),second).
Proof. reflexivity. Qed.

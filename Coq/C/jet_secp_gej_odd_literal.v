(** Literal LibSecp256k1.hs:565. Bridges used by the original C caller;
    this specification port by itself is not an implementation proof. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_secp_fe_math C.jet_secp_canonical_normalize
 C.jet_secp_canonical_zero C.jet_secp_canonical_odd C.jet_secp_rescale_literal
 C.jet_secp_negate_literal_contract C.jet_secp_multiply_literal_spec C.jet_secp_invert_literal C.jet_secp_eea_parametric
 C.jet_secp_curve_literal C.jet_secp_gej_norm_literal C.jet_secp_affine_inverse_literal
 C.jet_secp_decompress_literal C.jet_literal_division_parametric.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_gej_y_is_odd {term:Alg.Core.Algebra} :
 term(Ty.Prod(Ty.Prod(Word 8)(Word 8))(Word 8))Bit :=
 (O(I H) &&& (I H >>> @literal_fe_invert term >>> @literal_fe_cube term))
 >>> @literal_fe_multiply term >>> @canonical_fe_is_odd term.
Local Opaque literal_fe_invert literal_fe_cube literal_fe_multiply canonical_fe_is_odd literal_gej_norm.

Lemma literal_gej_y_is_odd_value (x y z:Ty.tySem(Word 8)) :
 @literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z)=
 @canonical_fe_is_odd Alg.CoreFunSem(snd(@literal_gej_norm Alg.CoreFunSem ((x,y),z))).
Proof. rewrite literal_gej_norm_step;reflexivity. Qed.

Lemma literal_gej_y_is_odd_encoded (x y z:Ty.tySem(Word 8)) :
 Simplicity.Translate.encode(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))=
 (Some(Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z)))::nil)%list.
Proof. destruct(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z));reflexivity. Qed.

Lemma literal_gej_y_is_odd_numeric (x y z:Ty.tySem(Word 8)) :
 Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))=
 Z.testbit((@toZ(WordToZ 8)y*literal_invert_numeric(@toZ(WordToZ 8)z)*
  literal_invert_numeric(@toZ(WordToZ 8)z)*literal_invert_numeric(@toZ(WordToZ 8)z)) mod feP)0.
Proof.
 rewrite literal_gej_y_is_odd_value,canonical_fe_is_odd_numeric,canonical_fe_normalize_numeric,
  canonical_field_order_matches_limb_model.
 pose proof(literal_gej_norm_numeric x y z) as Numeric.
 destruct(@literal_gej_norm Alg.CoreFunSem ((x,y),z)) as[ox oy].
 cbn [snd] in *;unfold literal_gej_norm_numeric_value in Numeric;injection Numeric as EX EY.
 rewrite EY,Z.mod_mod by(unfold feP,feR;lia);reflexivity.
Qed.

Lemma literal_gej_y_is_odd_infinity (x y z:Ty.tySem(Word 8)) :
 Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)=Datatypes.true ->
 Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))=Datatypes.false.
Proof.
 intro Zero;pose proof(canonical_fe_zero_after_normalize z) as NormalZero.
 rewrite Zero in NormalZero;apply Z.eqb_eq in NormalZero.
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model in NormalZero.
 rewrite literal_gej_y_is_odd_numeric.
 rewrite <-(literal_invert_numeric_mod_field(@toZ(WordToZ 8)z)ltac:(apply word_toZ_range)),
  NormalZero,literal_invert_numeric_zero,!Z.mul_0_r,Z.mod_0_l by(unfold feP,feR;lia).
 reflexivity.
Qed.

Lemma literal_gej_y_is_odd_parametric : Alg.Core.Parametric(@literal_gej_y_is_odd).
Proof.
 intros t1 t2 R;unfold literal_gej_y_is_odd.
 repeat first[apply decompress_odd_parametric|apply literal_fe_multiply_parametric|
  apply literal_fe_invert_parametric|apply curve_cube_parametric|apply Alg.comp_Parametric|
  apply Alg.pair_Parametric|apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.

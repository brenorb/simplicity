(** The literal mixed-addition operand for arbitrary shared Z. *)
From Coq Require Import ZArith Lia Ring.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_weak_loose C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_dispatch_literal C.jet_secp_curve_literal C.jet_secp_canonical_zero
 C.jet_secp_mixed_nonzero_literal C.jet_secp_zinv_differences C.jet_secp_zinv_general_numeric
 C.jet_secp_rescale_literal C.jet_secp_multiply_literal_spec C.jet_secp_square_execution
 C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words weak_loose_words literal_fe_multiply literal_fe_square literal_fe_cube.

Lemma zinv_scaled_x_numeric bx byword s :
 @toZ (WordToZ 8) (fst (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)))=
 (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) s*@toZ (WordToZ 8) s) mod feP.
Proof.
 change (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
  (bx,@literal_fe_square Alg.CoreFunSem s))=
  (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) s*@toZ (WordToZ 8) s) mod feP).
 rewrite literal_multiply_numeric,literal_square_numeric,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 f_equal;ring.
Qed.

Lemma zinv_scaled_y_numeric bx byword s :
 @toZ (WordToZ 8) (snd (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)))=
 (@toZ (WordToZ 8) byword*@toZ (WordToZ 8) s*@toZ (WordToZ 8) s*@toZ (WordToZ 8) s) mod feP.
Proof.
 change (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
  (byword,@literal_fe_cube Alg.CoreFunSem s))=
  (@toZ (WordToZ 8) byword*@toZ (WordToZ 8) s*@toZ (WordToZ 8) s*@toZ (WordToZ 8) s) mod feP).
 rewrite literal_multiply_numeric,literal_curve_cube_numeric,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 f_equal;ring.
Qed.

Theorem zinv_differences_scaled_literal x y z u v inv (ax ay az bx byword s : Ty.tySem (Word 8)) :
 (forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60) ->
 (forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60) ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 radix_value (zinv_h_words x z u inv) mod feP=
  (-@toZ (WordToZ 8) (mixed_literal_h ax az (fst (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))))) mod feP /\
 radix_value (zinv_i_words y z v inv) mod feP=
  @toZ (WordToZ 8) (mixed_literal_i ay az (snd (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)))) mod feP /\
 square_input_bounds (zinv_h_words x z u inv) /\ square_input_bounds (zinv_i_words y z v inv).
Proof.
 intros BX BY BZ BU BV BI Scale HX HY HZ HU HV.
 destruct (zinv_differences_value x y z u v inv BX BY BZ BU BV BI) as (HRaw & IRaw & BH & BIW).
 pose (sx:=fst (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))).
 pose (sy:=snd (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))).
 assert (SX:(radix_value u*radix_value inv*radix_value inv) mod feP=@toZ (WordToZ 8) sx mod feP).
 { unfold sx;rewrite zinv_scaled_x_numeric,Z.mod_mod by (unfold feP,feR;lia).
   apply double_residue_product;[apply double_residue_product;assumption|exact Scale]. }
 assert (SY:(radix_value v*radix_value inv*radix_value inv*radix_value inv) mod feP=@toZ (WordToZ 8) sy mod feP).
 { unfold sy;rewrite zinv_scaled_y_numeric,Z.mod_mod by (unfold feP,feR;lia).
   apply double_residue_product;[|exact Scale].
   apply double_residue_product;[|exact Scale].
   apply double_residue_product;assumption. }
 assert (HUZ:(radix_value u*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) mod feP=
  (@toZ (WordToZ 8) sx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP).
 { replace (radix_value u*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) with
    ((radix_value u*radix_value inv*radix_value inv)*radix_value z*radix_value z) by ring.
   apply double_residue_product;[apply double_residue_product;assumption|exact HZ]. }
 assert (HVZ:(radix_value v*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) mod feP=
  (@toZ (WordToZ 8) sy*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP).
 { replace (radix_value v*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)) with
    ((radix_value v*radix_value inv*radix_value inv*radix_value inv)*radix_value z*radix_value z*radix_value z) by ring.
   apply double_residue_product;[|exact HZ].
   apply double_residue_product;[|exact HZ].
   apply double_residue_product;assumption. }
 fold sx sy.
 split.
 - rewrite HRaw,mixed_literal_h_numeric.
   change ((radix_value u*(radix_value z*radix_value inv)*(radix_value z*radix_value inv)-radix_value x) mod feP=
    (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) sx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP) mod feP).
   rewrite Zminus_mod_idemp_r.
   replace (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) sx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az)) with
    (@toZ (WordToZ 8) sx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az-@toZ (WordToZ 8) ax) by ring.
   apply mixed_residue_difference;assumption.
 - split.
   + rewrite IRaw,mixed_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
     apply mixed_residue_difference;assumption.
   + split;assumption.
Qed.

Theorem zinv_tests_scaled_literal x y z u v inv (ax ay az bx byword s : Ty.tySem (Word 8)) :
 (forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60) ->
 (forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60) ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0=
  Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az (fst (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))))) /\
 Z.eqb (radix_value (zinv_i_words y z v inv) mod feP) 0=
  Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az (snd (@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s))))).
Proof.
 intros BX BY BZ BU BV BI Scale HX HY HZ HU HV.
 destruct (zinv_differences_scaled_literal x y z u v inv ax ay az bx byword s BX BY BZ BU BV BI Scale HX HY HZ HU HV)
  as (HDiff & IDiff & BH & BIW).
 split;rewrite literal_curve_zero_numeric.
 - rewrite HDiff;apply mixed_negated_zero_test.
 - rewrite IDiff;reflexivity.
Qed.

(** The actual loose zinv H/I words and the fixed literal Simplicity tests. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_weak_loose C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_dispatch_literal C.jet_secp_curve_literal C.jet_secp_canonical_zero
 C.jet_secp_mixed_nonzero_literal C.jet_secp_zinv_differences C.jet_secp_zinv_one_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque point_mul_words weak_loose_words.

Theorem zinv_differences_literal x y z u v inv (ax ay az bx byword : Ty.tySem (Word 8)) :
 (forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60) ->
 (forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60) ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value inv mod feP=1 ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 radix_value (zinv_h_words x z u inv) mod feP=(-@toZ (WordToZ 8) (mixed_literal_h ax az bx)) mod feP /\
 radix_value (zinv_i_words y z v inv) mod feP=@toZ (WordToZ 8) (mixed_literal_i ay az byword) mod feP /\
 square_input_bounds (zinv_h_words x z u inv) /\ square_input_bounds (zinv_i_words y z v inv).
Proof.
 intros BX BY BZ BU BV BI One HX HY HZ HU HV.
 destruct (zinv_differences_one x y z u v inv BX BY BZ BU BV BI One) as (HRaw & IRaw & BH & BIW).
 assert (HUZ : (radix_value u*radix_value z*radix_value z) mod feP=
   (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP).
 { apply double_residue_product;[apply double_residue_product;assumption|exact HZ]. }
 assert (HVZ : (radix_value v*radix_value z*radix_value z*radix_value z) mod feP=
   (@toZ (WordToZ 8) byword*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP).
 { apply double_residue_product.
   - apply double_residue_product;[apply double_residue_product;assumption|exact HZ].
   - exact HZ. }
 split.
 - rewrite HRaw,mixed_literal_h_numeric.
   change ((radix_value u*radix_value z*radix_value z-radix_value x) mod feP=
     (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP) mod feP).
   rewrite Zminus_mod_idemp_r.
   replace (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az)) with
     (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az-@toZ (WordToZ 8) ax) by ring.
   apply mixed_residue_difference;assumption.
 - split.
   + rewrite IRaw,mixed_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
     apply mixed_residue_difference;assumption.
   + split;assumption.
Qed.

Theorem zinv_tests_literal x y z u v inv (ax ay az bx byword : Ty.tySem (Word 8)) :
 (forall j,(j<5)%nat -> Int64.unsigned (x j)<=2^60) ->
 (forall j,(j<5)%nat -> Int64.unsigned (y j)<=2^60) ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value inv mod feP=1 ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0=
   Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) /\
 Z.eqb (radix_value (zinv_i_words y z v inv) mod feP) 0=
   Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)).
Proof.
 intros BX BY BZ BU BV BI One HX HY HZ HU HV.
 destruct (zinv_differences_literal x y z u v inv ax ay az bx byword BX BY BZ BU BV BI One HX HY HZ HU HV)
   as (HDiff & IDiff & BH & BIW).
 split;rewrite literal_curve_zero_numeric.
 - rewrite HDiff;apply mixed_negated_zero_test.
 - rewrite IDiff;reflexivity.
Qed.

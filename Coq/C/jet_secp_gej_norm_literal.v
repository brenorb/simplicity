(** Literal LibSecp256k1.zinv/gej_norm (lines763--765), with exact numeric
    coordinate outputs derived from the literal EEA-based inversion. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_invert_literal C.jet_secp_eea_parametric C.jet_secp_negate_literal_contract
 C.jet_secp_rescale_literal C.jet_secp_square_execution C.jet_secp_multiply_literal_spec
 C.jet_secp_curve_literal C.jet_secp_fe_math C.jet_toZ C.jet_secp_eea_literal C.jet_secp_eea_numeric
 C.jet_literal_division_parametric.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Opaque literal_fe_invert literal_fe_multiply literal_fe_square literal_fe_cube.

Definition literal_gej_norm {term : Alg.Core.Algebra} :
 term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8)) :=
 (O H &&& I (@literal_fe_invert term)) >>> @literal_gej_zinv term.
Definition literal_gej_norm_numeric_value x y z :=
 let iz:=literal_invert_numeric z in ((x*iz*iz) mod feP,(y*iz*iz*iz) mod feP).

Lemma literal_gej_norm_step (x y z : Ty.tySem (Word 8)) :
 @literal_gej_norm Alg.CoreFunSem ((x,y),z)=
 (@literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_invert Alg.CoreFunSem z)),
  @literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_invert Alg.CoreFunSem z))).
Proof. reflexivity. Qed.

Theorem literal_gej_norm_numeric (x y z : Ty.tySem (Word 8)) :
 let '(rx,ry):=@literal_gej_norm Alg.CoreFunSem ((x,y),z) in
 (@toZ (WordToZ 8) rx,@toZ (WordToZ 8) ry)=
 literal_gej_norm_numeric_value (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z).
Proof.
 rewrite literal_gej_norm_step.
 rewrite !literal_multiply_numeric,literal_square_numeric,literal_curve_cube_numeric,literal_fe_invert_numeric.
 rewrite !Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 unfold literal_gej_norm_numeric_value;f_equal;f_equal;ring.
Qed.

Theorem literal_gej_norm_word (x y z : Ty.tySem (Word 8)) :
 @literal_gej_norm Alg.CoreFunSem ((x,y),z)=
 (@fromZ (WordToZ 8) (fst (literal_gej_norm_numeric_value (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z))),
  @fromZ (WordToZ 8) (snd (literal_gej_norm_numeric_value (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z)))).
Proof.
 pose proof (literal_gej_norm_numeric x y z) as Coords.
 destruct (@literal_gej_norm Alg.CoreFunSem ((x,y),z)) as [rx ry].
 destruct (literal_gej_norm_numeric_value (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z)) as [nx ny].
 injection Coords as HX HY;cbn [fst snd].
 rewrite <-HX,<-HY,!from_toZ;reflexivity.
Qed.

Lemma literal_gej_norm_numeric_one x y :
 literal_gej_norm_numeric_value x y 1=(x mod feP,y mod feP).
Proof. unfold literal_gej_norm_numeric_value;rewrite literal_invert_numeric_one;rewrite !Z.mul_1_r;reflexivity. Qed.

Lemma literal_gej_zinv_parametric : Alg.Core.Parametric (@literal_gej_zinv).
Proof.
 intros t1 t2 R;unfold literal_gej_zinv.
 repeat first [apply curve_square_parametric | apply curve_cube_parametric |
   apply literal_fe_multiply_parametric | apply Alg.pair_Parametric | apply Alg.comp_Parametric |
   apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.iden_Parametric].
Qed.

Lemma literal_gej_norm_parametric : Alg.Core.Parametric (@literal_gej_norm).
Proof.
 intros t1 t2 R;unfold literal_gej_norm.
 apply Alg.comp_Parametric.
 - apply Alg.pair_Parametric;
     [apply Alg.take_Parametric;apply Alg.iden_Parametric|
      apply Alg.drop_Parametric;apply literal_fe_invert_parametric].
 - apply literal_gej_zinv_parametric.
Qed.

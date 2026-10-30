(** Pure bridge for finite-point/even-Y/X comparison; C execution is separate. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_curve_group_sign C.jet_secp_field_word_group C.jet_secp_jacobian_word_group
 C.jet_secp_jacobian_group C.jet_secp_table_pass2_group C.jet_secp_affine_word_valid
 C.jet_secp_even_decompress C.jet_secp_even_y_unique C.jet_secp_curve_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_gej_predicate C.jet_secp_linear_check_group
 C.jet_secp_canonical_normalize C.jet_secp_canonical_odd C.jet_secp_gej_norm_literal
 C.jet_secp_norm_group C.jet_secp_multiply_literal_spec C.jet_secp_decompress_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_even_x_test_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque secp_field_word literal_gej_is_infinity literal_gej_norm literal_decompress
 canonical_fe_is_odd canonical_fe_normalize literal_ge_is_on_curve.
Lemma secp_affine_word_rep_curve (x y:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_affine_word_rep (GZnZ.one feP) (x,y) p ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true.
Proof.
 intro Represented.
 pose proof (secp_affine_word_rep_finite x y p Represented) as Finite.
 destruct (secp_affine_word_rep_coordinates x y p Represented) as [X Y].
 destruct p as [|px py Curve];[contradiction|].
 cbn [secp_group_point_x secp_group_point_y] in X,Y;clear Represented Finite.
 rewrite X,Y in Curve;pose proof (secp_group_curve_numeric _ _ Curve) as Numeric.
 rewrite literal_ge_curve_numeric;apply Z.eqb_eq.
 Local Transparent secp_field_word.
 unfold secp_field_word,secp_field_integer in Numeric;cbn [GZnZ.val] in Numeric.
 rewrite !Z.mul_mod_idemp_l,!Z.mul_mod_idemp_r in Numeric by (pose proof secp_group_field_positive;lia).
 assert (Cubes:(@toZ (WordToZ 8) x mod feP*(@toZ (WordToZ 8) x mod feP)*(@toZ (WordToZ 8) x mod feP)) mod feP=
  (@toZ (WordToZ 8) x*@toZ (WordToZ 8) x*@toZ (WordToZ 8) x) mod feP).
 { symmetry;rewrite (Z.mul_mod (@toZ (WordToZ 8) x*@toZ (WordToZ 8) x) (@toZ (WordToZ 8) x) feP),
   (Z.mul_mod (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) x) feP),Z.mul_mod_idemp_l by (pose proof secp_group_field_positive;lia).
   reflexivity. }
 rewrite <-Z.add_mod_idemp_l,Cubes,Z.add_mod_idemp_l in Numeric by (pose proof secp_group_field_positive;lia).
 symmetry;exact Numeric.
Qed.
Lemma secp_gej_norm_ranges (x y z:Ty.tySem (Word 8)):
 let pair:=@literal_gej_norm Alg.CoreFunSem ((x,y),z) in
 0<=@toZ (WordToZ 8) (fst pair)<feP /\0<=@toZ (WordToZ 8) (snd pair)<feP.
Proof.
 rewrite literal_gej_norm_step;cbn [fst snd];rewrite !literal_multiply_numeric.
 split;apply Z.mod_pos_bound;pose proof secp_group_field_positive;lia.
Qed.
Definition secp_even_x_test (point:Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
 (r:Ty.tySem (Word 8)):bool:=
 if Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point) then Datatypes.false else
 let xy:=@literal_gej_norm Alg.CoreFunSem point in
 andb (negb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem (snd xy))))
  (Z.eqb (@toZ (WordToZ 8) (fst xy)) (@toZ (WordToZ 8) r)).
Lemma secp_affine_even_x_decompress (x y r:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true ->
 0<=@toZ (WordToZ 8) x<feP ->0<=@toZ (WordToZ 8) y<feP ->0<=@toZ (WordToZ 8) r<feP ->
 ((Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)=Datatypes.false /\x=r) <->
 @literal_decompress Alg.CoreFunSem (inl tt,r)=inr (x,y)).
Proof.
 intros Curve RangeX RangeY RangeR;split.
 - intros [Even Equal];subst r;apply secp_even_decompress_complete;assumption.
 - intro Output;destruct (secp_even_decompress_properties r x y Output) as [X [_ Even]].
   split;[exact Even|rewrite (secp_normalize_bounded_word r RangeR) in X;exact X].
Qed.
Theorem secp_even_x_test_group (x y z r:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_jacobian_word_rep (GZnZ.one feP) ((x,y),z) p ->0<=@toZ (WordToZ 8) r<feP ->
 (secp_even_x_test ((x,y),z) r=Datatypes.true <->
 exists rx ry:Ty.tySem (Word 8),
 @literal_decompress Alg.CoreFunSem (inl tt,r)=inr (rx,ry) /\
 secp_affine_word_rep (GZnZ.one feP) (rx,ry) p).
Proof.
 intros Represented RangeR;unfold secp_even_x_test.
 pose proof (secp_jacobian_word_infinity ((x,y),z) p Represented) as Infinity.
 destruct (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem ((x,y),z))) eqn:Flag.
 - split;[discriminate|].
   intros (rx & ry & Output & Affine).
   pose proof (secp_affine_word_rep_finite rx ry p Affine) as Finite.
   exfalso;apply Finite;apply (proj1 Infinity);reflexivity.
 - assert (ZNonzero:secp_field_word z<>GZnZ.zero feP).
   { intro Zero;apply (proj2 (C.jet_secp_jacobian_mixed_word_group.secp_field_word_flag_true z)) in Zero.
     rewrite literal_gej_is_infinity_value in Flag;congruence. }
   pose proof (secp_literal_gej_norm_group x y z p ZNonzero Represented) as Normalized.
   pose proof (secp_gej_norm_ranges x y z) as Ranges.
   destruct (@literal_gej_norm Alg.CoreFunSem ((x,y),z)) as [nx ny] eqn:Norm.
   cbn [fst snd] in Ranges|-*;destruct Ranges as [RangeX RangeY].
   split.
   + intro Match;apply Bool.andb_true_iff in Match;destruct Match as [Even X].
     apply Bool.negb_true_iff in Even;apply Z.eqb_eq in X.
     assert (Equal:nx=r) by (apply (toZ_injective (WordToZ 8));exact X).
     exists nx,ny;split;[|exact Normalized].
     apply (proj1 (secp_affine_even_x_decompress nx ny r
      (secp_affine_word_rep_curve nx ny p Normalized) RangeX RangeY RangeR));split;assumption.
   + intros (rx & ry & Output & Affine).
     destruct (secp_affine_word_same_point nx ny rx ry p Normalized Affine) as [X Y].
     destruct (secp_even_decompress_properties r rx ry Output) as [RX [RangeRY Even]].
     rewrite (secp_normalize_bounded_word r RangeR) in RX.
     subst rx;rewrite !secp_normalize_bounded_word in X,Y by assumption.
     subst nx;subst ny;rewrite Even;cbn [negb andb];apply Z.eqb_refl.
Qed.

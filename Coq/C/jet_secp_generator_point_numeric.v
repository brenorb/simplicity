(** Numeric evaluation of the fixed literal point operations, for closed
    table certificates. This is not a replacement point specification. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_generate_literal C.jet_secp_double_literal C.jet_secp_add_literal
 C.jet_secp_add_literal_step C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_nonzero_literal
 C.jet_secp_double_half_literal_numeric C.jet_secp_literal_add_numeric
 C.jet_secp_literal_add_program C.jet_secp_negate_literal_contract
 C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_curve_literal
 C.jet_secp_rescale_literal C.jet_secp_fe_math C.jet_toZ
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize
 C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_halve literal_fe_multiply_int literal_fe_multiply literal_fe_add
 literal_fe_negate literal_fe_square literal_gej_double_body literal_gej_double
 literal_gej_infinity literal_gej_is_infinity.

Definition literal_halve_numeric x :=
 if Z.eqb (x mod 2) 0 then x/2 else ((feP+1)/2+x/2) mod feP.

Lemma literal_halve_numeric_matches (a : Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a)=
 literal_halve_numeric (@toZ (WordToZ 8) a).
Proof.
 pose proof (double_half_shift_value a) as Shift;cbn zeta in Shift.
 rewrite literal_fe_halve_step.
 destruct (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)) as [q r] eqn:Half.
 cbn [fst snd] in Shift|-*.
 destruct r as [u | u];destruct u.
 - change (@toZ (WordToZ 8) a=2*@toZ (WordToZ 8) q+0) in Shift.
   pose proof (Z.div_unique _ 2 _ 0 ltac:(left;lia) Shift) as Quotient.
   pose proof (Z.mod_unique _ 2 _ 0 ltac:(left;lia) Shift) as Remainder.
   unfold literal_halve_numeric;rewrite <-Quotient,<-Remainder;reflexivity.
 - change (@toZ (WordToZ 8) a=2*@toZ (WordToZ 8) q+1) in Shift.
   pose proof (Z.div_unique _ 2 _ 1 ltac:(left;lia) Shift) as Quotient.
   pose proof (Z.mod_unique _ 2 _ 1 ltac:(left;lia) Shift) as Remainder.
   change (@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (double_half_word,q))=
     literal_halve_numeric (@toZ (WordToZ 8) a)).
   rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,double_half_word_value.
   unfold literal_halve_numeric;rewrite <-Quotient,<-Remainder;reflexivity.
Qed.


Definition literal_jacobian_denote (a : Ty.tySem literal_generator_jacobian) :=
 ((@toZ (WordToZ 8) (fst (fst a)),@toZ (WordToZ 8) (snd (fst a))),@toZ (WordToZ 8) (snd a)).
Definition literal_double_body_numeric x y z :=
 let s:=(y*y) mod feP in
 let l:=literal_halve_numeric ((3*((x*x) mod feP)) mod feP) in
 let t:=(feP-((s*x) mod feP)) mod feP in
 let rx:=(((2*t) mod feP)+((l*l) mod feP)) mod feP in
 ((rx,(feP-(((l*((rx+t) mod feP)) mod feP+(s*s) mod feP) mod feP)) mod feP),
  (y*z) mod feP).
Definition literal_double_numeric x y z :=
 if orb (Z.eqb z 0) (Z.eqb z feP) then ((0,0),0) else literal_double_body_numeric x y z.

Lemma literal_double_body_numeric_matches (x y z : Ty.tySem (Word 8)) :
 literal_jacobian_denote (@literal_gej_double_body Alg.CoreFunSem ((x,y),z))=
 literal_double_body_numeric (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z).
Proof.
 rewrite literal_gej_double_body_step;unfold literal_jacobian_denote;cbn zeta;cbn [fst snd].
 repeat first [rewrite literal_curve_negate_numeric | rewrite literal_fe_add_numeric |
   rewrite literal_multiply_numeric | rewrite literal_square_numeric |
   rewrite literal_fe_multiply_int_numeric | rewrite literal_halve_numeric_matches |
   rewrite canonical_field_order_matches_limb_model].
 reflexivity.
Qed.

Lemma literal_double_numeric_matches (x y z : Ty.tySem (Word 8)) :
 literal_jacobian_denote (@literal_gej_double Alg.CoreFunSem ((x,y),z))=
 literal_double_numeric (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z).
Proof.
 Local Transparent literal_gej_infinity.
 rewrite literal_gej_double_step,literal_gej_is_infinity_value,canonical_fe_is_zero_numeric,
   canonical_field_order_matches_limb_model.
 unfold literal_double_numeric.
 destruct (orb (Z.eqb (@toZ (WordToZ 8) z) 0) (Z.eqb (@toZ (WordToZ 8) z) feP)).
 - unfold literal_jacobian_denote,literal_gej_infinity,literal_fe_zero256;
     cbn [fst snd];rewrite Word.zero_correct;reflexivity.
 - apply literal_double_body_numeric_matches.
Qed.

Definition literal_zero_numeric z := orb (Z.eqb z 0) (Z.eqb z feP).
Definition literal_mixed_values x y z bx byword :=
 let u:=(x*((1*1) mod feP)) mod feP in
 let v:=(y*((1*1*1) mod feP)) mod feP in
 let h:=(u+(((feP-bx) mod feP)*((z*z) mod feP)) mod feP) mod feP in
 let i:=(v+(((feP-byword) mod feP)*((z*z*z) mod feP)) mod feP) mod feP in
 (u,v,h,i).
Definition literal_mixed_nonzero_numeric u v h i z :=
 let t:=(((h*h) mod feP)*u) mod feP in
 let g:=(h*h*h) mod feP in
 let rx:=((g+((-2*t) mod feP)) mod feP+(i*i) mod feP) mod feP in
 ((rx,((g*v) mod feP+(i*((rx+(feP-t) mod feP) mod feP)) mod feP) mod feP),
  (((h*z) mod feP)*((feP-1) mod feP)) mod feP).
Definition literal_mixed_numeric x y z bx byword :=
 if literal_zero_numeric z then ((bx mod feP,byword mod feP),1) else
 let '(u,v,h,i):=literal_mixed_values x y z bx byword in
 if literal_zero_numeric h then
   if literal_zero_numeric i then literal_double_numeric x y z else ((0,0),0)
 else literal_mixed_nonzero_numeric u v h i z.

Lemma literal_zero_numeric_matches (a : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem a)=
 literal_zero_numeric (@toZ (WordToZ 8) a).
Proof.
 rewrite canonical_fe_is_zero_numeric,canonical_field_order_matches_limb_model;reflexivity.
Qed.

Lemma literal_mixed_step (x y z bx byword : Ty.tySem (Word 8)) :
 let h:=mixed_literal_h x z bx in let i:=mixed_literal_i y z byword in
 let u:=@literal_fe_multiply Alg.CoreFunSem
   (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) in
 let v:=@literal_fe_multiply Alg.CoreFunSem
   (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) in
 @literal_gej_ge_add Alg.CoreFunSem (((x,y),z),(bx,byword))=
 if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z) then
   ((@canonical_fe_normalize Alg.CoreFunSem bx,@canonical_fe_normalize Alg.CoreFunSem byword),
    @canonical_fe_normalize Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))
 else if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem h) then
   if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem i) then
     @literal_gej_double Alg.CoreFunSem ((x,y),z)
   else @literal_gej_infinity Alg.CoreFunSem tt
 else ((mixed_literal_rx h i u,mixed_literal_ry h i u v),mixed_literal_rz h z).
Proof.
 cbn zeta;destruct (@canonical_fe_is_zero Alg.CoreFunSem z) as [q | q] eqn:ZFlag;destruct q.
 - assert (Finite : @literal_gej_is_infinity Alg.CoreFunSem ((x,y),z)=inl tt)
     by (rewrite literal_gej_is_infinity_value;exact ZFlag).
   assert (One : @literal_gej_is_infinity Alg.CoreFunSem
     ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
     by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
   rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
   cbn zeta;fold (mixed_literal_h x z bx) (mixed_literal_i y z byword).
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx)) as [q | q];destruct q;
     [reflexivity|].
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i y z byword)) as [q | q];destruct q;reflexivity.
 - apply literal_gej_ge_add_infinite;rewrite literal_gej_is_infinity_value;exact ZFlag.
Qed.

Lemma literal_mixed_values_numeric_matches (x y z bx byword : Ty.tySem (Word 8)) :
 (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
     (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))),
  @toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
     (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))),
  @toZ (WordToZ 8) (mixed_literal_h x z bx),@toZ (WordToZ 8) (mixed_literal_i y z byword))=
 literal_mixed_values (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z)
   (@toZ (WordToZ 8) bx) (@toZ (WordToZ 8) byword).
Proof.
 unfold mixed_literal_h,mixed_literal_i.
 repeat first [rewrite literal_curve_negate_numeric | rewrite literal_fe_add_numeric |
   rewrite literal_multiply_numeric | rewrite literal_square_numeric |
   rewrite literal_curve_cube_numeric | rewrite literal_fe_one256_value |
   rewrite canonical_field_order_matches_limb_model].
 reflexivity.
Qed.

Lemma literal_mixed_nonzero_numeric_matches (h i u v z : Ty.tySem (Word 8)) :
 literal_jacobian_denote ((mixed_literal_rx h i u,mixed_literal_ry h i u v),mixed_literal_rz h z)=
 literal_mixed_nonzero_numeric (@toZ (WordToZ 8) u) (@toZ (WordToZ 8) v)
   (@toZ (WordToZ 8) h) (@toZ (WordToZ 8) i) (@toZ (WordToZ 8) z).
Proof.
 unfold literal_jacobian_denote,mixed_literal_ry,mixed_literal_rz,
   mixed_literal_tx,mixed_literal_rx,mixed_literal_t;cbn [fst snd].
 repeat first [rewrite literal_curve_negate_numeric | rewrite literal_fe_add_numeric |
   rewrite literal_multiply_numeric | rewrite literal_square_numeric |
   rewrite literal_curve_cube_numeric | rewrite literal_fe_multiply_int_numeric |
   rewrite literal_fe_one256_value | rewrite canonical_field_order_matches_limb_model].
 reflexivity.
Qed.

Lemma literal_mixed_numeric_matches (x y z bx byword : Ty.tySem (Word 8)) :
 literal_jacobian_denote (@literal_gej_ge_add Alg.CoreFunSem (((x,y),z),(bx,byword)))=
 literal_mixed_numeric (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z)
   (@toZ (WordToZ 8) bx) (@toZ (WordToZ 8) byword).
Proof.
 rewrite literal_mixed_step;cbn zeta;unfold literal_mixed_numeric.
 rewrite <- (literal_mixed_values_numeric_matches x y z bx byword).
 rewrite <- !literal_zero_numeric_matches.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)).
 - unfold literal_jacobian_denote;cbn [fst snd].
   rewrite !canonical_fe_normalize_numeric,literal_fe_one256_value,canonical_field_order_matches_limb_model.
   rewrite (Z.mod_small 1 feP) by (unfold feP,feR;lia);reflexivity.
 - destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx))).
   + destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i y z byword))).
     * apply literal_double_numeric_matches.
     * unfold literal_jacobian_denote,literal_gej_infinity,literal_fe_zero256;
         cbn [fst snd];rewrite Word.zero_correct;reflexivity.
   + apply literal_mixed_nonzero_numeric_matches.
Qed.

(** The first addition of the original odd table takes its nonzero-H branch
    on every valid affine input. The root exclusion is a checked coefficient
    certificate; no table-denominator premise is imposed on the input. *)
From Coq Require Import ZArith Znumtheory Lia Ring Morphisms Setoid.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_field_prime
 C.jet_secp_table_affine_seed C.jet_secp_table_denominators C.jet_secp_polynomial
 C.jet_secp_curve_polynomial C.jet_secp_curve_literal
 C.jet_secp_double_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_mixed_dispatch_literal C.jet_secp_generator_point_numeric
 C.jet_secp_add_literal C.jet_secp_mixed_nonzero_literal C.jet_secp_multiply_literal_spec
 C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_double literal_gej_zinv literal_fe_one256 toZ
 literal_fe_multiply literal_fe_negate mixed_literal_h.

Section TableFirstAlgebra.
Local Lemma table_first_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_first_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
 as table_first_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
 as table_first_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
 as table_first_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_first_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_first_modring : table_first_ring (constants [Zcst]).

Lemma table_initial_h_identity x :
 eqm feP (4*(x*table_curve_s x-table_double_x x)) (3*x*(x*x*x+28)).
Proof.
 unfold table_double_x,table_double_slope,table_curve_s.
 setoid_replace (4*(x*(x*x*x+7)-(3*x*x*table_half*(3*x*x*table_half)-2*x*(x*x*x+7))))
   with (12*x*(x*x*x+7)-9*x*x*x*x*(2*table_half)*(2*table_half)) by ring.
 setoid_rewrite table_half_inverse;ring.
Qed.

Theorem table_initial_h_nonzero x y :
 (x*x*x+7) mod feP=(y*y) mod feP ->
 (x*table_curve_s x-table_double_x x) mod feP<>0.
Proof.
 intro Curve.
 pose proof (table_denominator3_nonzero x y Curve) as Q.
 cbn [table_q3 polynomial_value] in Q.
 rewrite Z.mul_0_r,Z.add_0_r,Z.mul_1_r in Q.
 assert (Product:(3*x*(x*x*x+28)) mod feP<>0).
 { apply secp256k1_nonzero_product.
   - apply secp256k1_nonzero_product.
     + vm_compute;discriminate.
     + exact (secp_curve_x_nonzero x y Curve).
   - rewrite Z.add_comm;exact Q. }
 intro Zero;apply Product.
 pose proof (table_initial_h_identity x) as Identity;unfold eqm in Identity.
 rewrite <-Identity,Z.mul_mod,Zero,Z.mul_0_r,Z.mod_0_l by (unfold feP,feR;lia).
 reflexivity.
Qed.

Theorem literal_table_affine_first_h (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=true ->
 let d:=@literal_gej_double Alg.CoreFunSem ((x,y),@literal_fe_one256 Alg.CoreFunSem tt) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((x,y),snd d) in
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (mixed_literal_h (fst seed) (@literal_fe_one256 Alg.CoreFunSem tt) (fst (fst d))))=false.
Proof.
 intro Valid;cbn zeta.
 destruct (literal_table_affine_double x y Valid) as (DX & DY & DZ).
 destruct (literal_table_affine_seed x y Valid) as (SX & SY & Finite).
 set (d:=@literal_gej_double Alg.CoreFunSem ((x,y),@literal_fe_one256 Alg.CoreFunSem tt)) in *.
 set (seed:=@literal_gej_zinv Alg.CoreFunSem ((x,y),snd d)) in *.
 rewrite literal_curve_zero_numeric,mixed_literal_h_numeric,literal_fe_one256_value.
 rewrite !Z.mul_1_r,Z.mod_mod by (unfold feP,feR;lia).
 apply Z.eqb_neq.
 assert (HResidue:eqm feP
   (@toZ (WordToZ 8) (fst seed)-@toZ (WordToZ 8) (fst (fst d)))
   (@toZ (WordToZ 8) x*table_curve_s (@toZ (WordToZ 8) x)-table_double_x (@toZ (WordToZ 8) x))).
 { apply Zminus_eqm;assumption. }
 unfold eqm in HResidue;rewrite HResidue.
 apply (table_initial_h_nonzero _ (@toZ (WordToZ 8) y)).
 exact (literal_table_affine_curve x y Valid).
Qed.
Lemma literal_table_mixed_nonzero_z (x y z bx byword:Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx))=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (snd (@literal_gej_ge_add Alg.CoreFunSem (((x,y),z),(bx,byword)))))=false.
Proof.
 intros NonzeroZ NonzeroH.
 rewrite literal_mixed_step;cbn zeta;rewrite NonzeroZ,NonzeroH;cbn [fst snd].
 unfold mixed_literal_rz.
 rewrite literal_curve_zero_numeric,!literal_multiply_numeric,
   literal_curve_negate_numeric,literal_fe_one256_value.
 repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
 repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
 rewrite Z.mod_mod by (unfold feP,feR;lia).
 apply Z.eqb_neq;apply secp256k1_nonzero_negative_product;
   rewrite literal_curve_zero_numeric in NonzeroZ,NonzeroH;
   apply Z.eqb_neq;assumption.
Qed.

Lemma literal_table_mixed_point_projection
 (a:Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
 (b:Ty.tySem (Ty.Prod (Word 8) (Word 8))) :
 snd (@literal_gej_ge_add_ex Alg.CoreFunSem (a,b))=@literal_gej_ge_add Alg.CoreFunSem (a,b).
Proof. reflexivity. Qed.

Theorem literal_table_affine_first_z (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=true ->
 let d:=@literal_gej_double Alg.CoreFunSem ((x,y),@literal_fe_one256 Alg.CoreFunSem tt) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((x,y),snd d) in
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (snd (snd (@literal_gej_ge_add_ex Alg.CoreFunSem
     ((seed,@literal_fe_one256 Alg.CoreFunSem tt),fst d)))))=false.
Proof.
 intro Valid;cbn zeta.
 pose proof (literal_table_affine_first_h x y Valid) as HNonzero;cbn zeta in HNonzero.
 set (d:=@literal_gej_double Alg.CoreFunSem ((x,y),@literal_fe_one256 Alg.CoreFunSem tt)) in *.
 set (seed:=@literal_gej_zinv Alg.CoreFunSem ((x,y),snd d)) in *.
 rewrite literal_table_mixed_point_projection.
 destruct seed as [sx sy];destruct (fst d) as [bx byword].
 apply literal_table_mixed_nonzero_z.
 - rewrite mixed_literal_one_finite;reflexivity.
 - exact HNonzero.
Qed.
End TableFirstAlgebra.

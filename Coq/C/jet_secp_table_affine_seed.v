(** Connect the valid affine input to the original odd-table seed and doubled
    increment. These are residue facts about the literal operations, not a
    replacement table or an additional premise for a public jet. *)
From Coq Require Import ZArith Znumtheory Lia Ring Morphisms Setoid.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_literal
 C.jet_secp_curve_polynomial C.jet_secp_curve_nonzero
 C.jet_secp_double_literal C.jet_secp_double_half_literal_numeric
 C.jet_secp_rescale_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_multiply_literal_spec C.jet_secp_square_execution
 C.jet_secp_negate_literal_contract C.jet_secp_literal_gej_predicate
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_halve literal_fe_multiply_int literal_fe_multiply
 literal_fe_add literal_fe_negate literal_fe_square literal_fe_cube
 literal_fe_one256 literal_gej_double literal_gej_double_body literal_gej_zinv toZ.

Definition table_half := (feP+1)/2.
Definition table_curve_s x := x*x*x+7.
Definition table_double_slope x := 3*x*x*table_half.
Definition table_double_x x :=
 table_double_slope x*table_double_slope x-2*x*table_curve_s x.
Definition table_double_y x :=
 table_double_slope x*(3*x*table_curve_s x-table_double_slope x*table_double_slope x)
 -table_curve_s x*table_curve_s x.

Section TableSeedAlgebra.
Local Lemma table_mod_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_mod_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
 as table_mod_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
 as table_mod_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
 as table_mod_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_mod_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_modring : table_mod_ring (constants [Zcst]).

Lemma table_modulo_residue a : eqm feP (a mod feP) a.
Proof. unfold eqm;apply Z.mod_mod;unfold feP,feR;lia. Qed.
Lemma table_half_inverse : eqm feP (2*table_half) 1.
Proof. unfold eqm,table_half;vm_compute;reflexivity. Qed.

Lemma table_prime_residue : eqm feP feP 0.
Proof. unfold eqm;rewrite Z.mod_same,Z.mod_0_l by (unfold feP,feR;lia);reflexivity. Qed.
Local Opaque feP table_half.

Lemma literal_table_halve_residue (a:Ty.tySem (Word 8)) :
 eqm feP (@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a))
   (@toZ (WordToZ 8) a*table_half).
Proof.
 pose proof (literal_fe_halve_double a) as Half.
 change (eqm feP (2*@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a))
   (@toZ (WordToZ 8) a)) in Half.
 transitivity (@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a)*(2*table_half)).
 - setoid_rewrite table_half_inverse;ring.
 - setoid_replace
     (@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a)*(2*table_half)) with
     ((2*@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a))*table_half) by ring.
   setoid_rewrite Half;reflexivity.
Qed.

Lemma literal_table_add_residue (a b:Ty.tySem (Word 8)) u v :
 eqm feP (@toZ (WordToZ 8) a) u -> eqm feP (@toZ (WordToZ 8) b) v ->
 eqm feP (@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (a,b))) (u+v).
Proof.
 intros A B;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model.
 transitivity (@toZ (WordToZ 8) a+@toZ (WordToZ 8) b).
 - apply table_modulo_residue.
 - apply Zplus_eqm;assumption.
Qed.
Lemma literal_table_mul_residue (a b:Ty.tySem (Word 8)) u v :
 eqm feP (@toZ (WordToZ 8) a) u -> eqm feP (@toZ (WordToZ 8) b) v ->
 eqm feP (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (a,b))) (u*v).
Proof.
 intros A B;rewrite literal_multiply_numeric.
 transitivity (@toZ (WordToZ 8) a*@toZ (WordToZ 8) b).
 - apply table_modulo_residue.
 - apply Zmult_eqm;assumption.
Qed.
Lemma literal_table_square_residue (a:Ty.tySem (Word 8)) u :
 eqm feP (@toZ (WordToZ 8) a) u ->
 eqm feP (@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem a)) (u*u).
Proof.
 intro A;rewrite literal_square_numeric.
 transitivity (@toZ (WordToZ 8) a*@toZ (WordToZ 8) a).
 - apply table_modulo_residue.
 - apply Zmult_eqm;assumption.
Qed.
Lemma literal_table_scale_residue n (a:Ty.tySem (Word 8)) u :
 eqm feP (@toZ (WordToZ 8) a) u ->
 eqm feP (@toZ (WordToZ 8) (@literal_fe_multiply_int n Alg.CoreFunSem a)) (n*u).
Proof.
 intro A;rewrite literal_fe_multiply_int_numeric.
 transitivity (n*@toZ (WordToZ 8) a).
 - apply table_modulo_residue.
 - apply Zmult_eqm;[reflexivity|exact A].
Qed.
Lemma literal_table_negate_residue (a:Ty.tySem (Word 8)) u :
 eqm feP (@toZ (WordToZ 8) a) u ->
 eqm feP (@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem a)) (-u).
Proof.
 intro A;rewrite literal_curve_negate_numeric.
 transitivity (feP-@toZ (WordToZ 8) a);[apply table_modulo_residue|].
 change (eqm feP (feP-@toZ (WordToZ 8) a) (0-u)).
 apply Zminus_eqm;[exact table_prime_residue|exact A].
Qed.

Lemma literal_table_affine_curve (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=true ->
 eqm feP (table_curve_s (@toZ (WordToZ 8) x))
   (@toZ (WordToZ 8) y*@toZ (WordToZ 8) y).
Proof.
 rewrite literal_ge_curve_numeric;intro Curve;apply Z.eqb_eq in Curve.
 symmetry;exact Curve.
Qed.

Theorem literal_table_affine_coordinates_nonzero (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=true ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem x)=false /\
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem y)=false.
Proof.
 intro Valid;pose proof (literal_table_affine_curve x y Valid) as Curve.
 rewrite !literal_curve_zero_numeric;split;apply Z.eqb_neq.
 - exact (secp_curve_x_nonzero _ _ Curve).
 - exact (secp_curve_y_nonzero _ _ Curve).
Qed.

Theorem literal_table_affine_double (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=true ->
 let d:=@literal_gej_double Alg.CoreFunSem
   ((x,y),@literal_fe_one256 Alg.CoreFunSem tt) in
 eqm feP (@toZ (WordToZ 8) (fst (fst d))) (table_double_x (@toZ (WordToZ 8) x)) /\
 eqm feP (@toZ (WordToZ 8) (snd (fst d))) (table_double_y (@toZ (WordToZ 8) x)) /\
 eqm feP (@toZ (WordToZ 8) (snd d)) (@toZ (WordToZ 8) y).
Proof.
 intro Valid;cbn zeta.
 assert (Finite:Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
   ((x,y),@literal_fe_one256 Alg.CoreFunSem tt))=false).
 { rewrite literal_gej_is_infinity_value,literal_curve_zero_numeric,literal_fe_one256_value.
   vm_compute;reflexivity. }
 rewrite literal_gej_double_step,Finite,literal_gej_double_body_step.
 cbn zeta;cbn [fst snd].
 pose proof (literal_table_affine_curve x y Valid) as Curve.
 set (s:=@literal_fe_square Alg.CoreFunSem y).
 set (l:=@literal_fe_halve Alg.CoreFunSem
   (@literal_fe_multiply_int 3 Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem x))).
 set (t:=@literal_fe_negate Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (s,x))).
 set (rx:=@literal_fe_add Alg.CoreFunSem
   (@literal_fe_multiply_int 2 Alg.CoreFunSem t,@literal_fe_square Alg.CoreFunSem l)).
 fold s l t rx.
 assert (S:eqm feP (@toZ (WordToZ 8) s) (table_curve_s (@toZ (WordToZ 8) x))).
 { unfold s;pose proof (literal_table_square_residue y _ (eqm_refl feP (@toZ (WordToZ 8) y))) as YY.
   transitivity (@toZ (WordToZ 8) y*@toZ (WordToZ 8) y);[exact YY|symmetry;exact Curve]. }
 assert (L:eqm feP (@toZ (WordToZ 8) l) (table_double_slope (@toZ (WordToZ 8) x))).
 { unfold l,table_double_slope.
   transitivity (@toZ (WordToZ 8)
     (@literal_fe_multiply_int 3 Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem x))*table_half).
   - apply literal_table_halve_residue.
   - replace (3*@toZ (WordToZ 8) x*@toZ (WordToZ 8) x*table_half) with
       ((3*(@toZ (WordToZ 8) x*@toZ (WordToZ 8) x))*table_half) by (rewrite Z.mul_assoc;reflexivity).
     apply Zmult_eqm;[apply literal_table_scale_residue;apply literal_table_square_residue|];reflexivity. }
 assert (T:eqm feP (@toZ (WordToZ 8) t)
   (-(table_curve_s (@toZ (WordToZ 8) x)*@toZ (WordToZ 8) x))).
 { unfold t;apply literal_table_negate_residue;apply literal_table_mul_residue;[exact S|reflexivity]. }
 assert (RX:eqm feP (@toZ (WordToZ 8) rx) (table_double_x (@toZ (WordToZ 8) x))).
 { unfold rx;transitivity (2*(-(table_curve_s (@toZ (WordToZ 8) x)*@toZ (WordToZ 8) x))+
     table_double_slope (@toZ (WordToZ 8) x)*table_double_slope (@toZ (WordToZ 8) x)).
   - apply literal_table_add_residue.
     + apply literal_table_scale_residue;exact T.
     + apply literal_table_square_residue;exact L.
   - unfold table_double_x;ring. }
 split;[exact RX|];split.
 - transitivity (-(table_double_slope (@toZ (WordToZ 8) x)*
     (table_double_x (@toZ (WordToZ 8) x)-(table_curve_s (@toZ (WordToZ 8) x)*@toZ (WordToZ 8) x))+
     table_curve_s (@toZ (WordToZ 8) x)*table_curve_s (@toZ (WordToZ 8) x))).
   + apply literal_table_negate_residue;apply literal_table_add_residue.
     * apply literal_table_mul_residue;[exact L|].
       change (eqm feP (@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (rx,t)))
         (table_double_x (@toZ (WordToZ 8) x)+(-(table_curve_s (@toZ (WordToZ 8) x)*@toZ (WordToZ 8) x)))).
       apply literal_table_add_residue;assumption.
     * apply literal_table_square_residue;exact S.
   + unfold table_double_y,table_double_x;ring.
 - transitivity (@toZ (WordToZ 8) y*1);[apply literal_table_mul_residue|ring].
   + reflexivity.
   + rewrite literal_fe_one256_value;reflexivity.
Qed.
Lemma literal_table_zinv_residue (x y z:Ty.tySem (Word 8)) vx vy vz :
 eqm feP (@toZ (WordToZ 8) x) vx ->
 eqm feP (@toZ (WordToZ 8) y) vy ->
 eqm feP (@toZ (WordToZ 8) z) vz ->
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((x,y),z) in
 eqm feP (@toZ (WordToZ 8) (fst seed)) (vx*vz*vz) /\
 eqm feP (@toZ (WordToZ 8) (snd seed)) (vy*vz*vz*vz).
Proof.
 intros X Y Z;cbn zeta.
 change (eqm feP (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
   (x,@literal_fe_square Alg.CoreFunSem z))) (vx*vz*vz) /\
   eqm feP (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
   (y,@literal_fe_cube Alg.CoreFunSem z))) (vy*vz*vz*vz)).
 split.
 - transitivity (vx*(vz*vz)).
   + apply literal_table_mul_residue;[exact X|apply literal_table_square_residue;exact Z].
   + ring.
 - transitivity (vy*(vz*vz*vz)).
   + apply literal_table_mul_residue;[exact Y|].
     rewrite literal_curve_cube_numeric;transitivity
       (@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z).
     * apply table_modulo_residue.
     * apply Zmult_eqm;[apply Zmult_eqm|];assumption.
   + ring.
Qed.

Theorem literal_table_affine_seed (x y:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=true ->
 let d:=@literal_gej_double Alg.CoreFunSem
   ((x,y),@literal_fe_one256 Alg.CoreFunSem tt) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((x,y),snd d) in
 eqm feP (@toZ (WordToZ 8) (fst seed))
   (@toZ (WordToZ 8) x*table_curve_s (@toZ (WordToZ 8) x)) /\
 eqm feP (@toZ (WordToZ 8) (snd seed))
   (table_curve_s (@toZ (WordToZ 8) x)*table_curve_s (@toZ (WordToZ 8) x)) /\
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (snd d))=false.
Proof.
 intro Valid;cbn zeta.
 destruct (literal_table_affine_double x y Valid) as (DX & DY & DZ).
 pose proof (literal_table_affine_curve x y Valid) as Curve.
 destruct (literal_table_zinv_residue x y _ _ _ _
   (eqm_refl feP (@toZ (WordToZ 8) x)) (eqm_refl feP (@toZ (WordToZ 8) y)) DZ)
   as [SX SY].
 split.
 - transitivity (@toZ (WordToZ 8) x*@toZ (WordToZ 8) y*@toZ (WordToZ 8) y);[exact SX|].
   transitivity (@toZ (WordToZ 8) x*(@toZ (WordToZ 8) y*@toZ (WordToZ 8) y));[ring|].
   apply Zmult_eqm;[reflexivity|symmetry;exact Curve].
 - split.
   + transitivity (@toZ (WordToZ 8) y*@toZ (WordToZ 8) y*@toZ (WordToZ 8) y*@toZ (WordToZ 8) y);[exact SY|].
     transitivity ((@toZ (WordToZ 8) y*@toZ (WordToZ 8) y)*(@toZ (WordToZ 8) y*@toZ (WordToZ 8) y));[ring|].
     apply Zmult_eqm;symmetry;exact Curve.
   + rewrite literal_curve_zero_numeric;unfold eqm in DZ;rewrite DZ.
     rewrite <-literal_curve_zero_numeric.
     exact (proj2 (literal_table_affine_coordinates_nonzero x y Valid)).
Qed.
End TableSeedAlgebra.

(** Evaluation of the checked coefficient witnesses in the fixed field.
    This connects coefficient computations to the numeric literal-step
    formulas; it does not assert an additional public jet precondition. *)
From Coq Require Import ZArith Znumtheory Lia Ring Morphisms Setoid.
Require Import C.jet_secp_fe_math C.jet_secp_polynomial C.jet_secp_fast_polynomial
 C.jet_secp_table_coordinates C.jet_secp_table_affine_seed C.jet_secp_table_scaled_step.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque polynomial_value.
Section TableCoordinateValues.
Local Lemma table_values_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_values_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_values_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_values_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_values_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_values_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_values_modring : table_values_ring (constants [Zcst]).

Lemma table_fast_scale_value k p x :
 eqm feP (polynomial_value (fast_polynomial_scale k p) x) (k*polynomial_value p x).
Proof.
 unfold eqm;rewrite fast_polynomial_scale_correct;apply polynomial_scale_value;unfold feP,feR;lia.
Qed.
Lemma table_fast_mul_value p q x :
 eqm feP (polynomial_value (fast_polynomial_mul p q) x)
   (polynomial_value p x*polynomial_value q x).
Proof.
 unfold eqm;rewrite fast_polynomial_mul_correct;apply polynomial_mul_value;unfold feP,feR;lia.
Qed.
Lemma table_fast_sub_value p q x :
 eqm feP (polynomial_value (fast_polynomial_sub p q) x)
   (polynomial_value p x-polynomial_value q x).
Proof.
 unfold eqm;rewrite fast_polynomial_sub_correct;apply polynomial_sub_value;unfold feP,feR;lia.
Qed.
Lemma table_witness_sq_value p x :
 eqm feP (polynomial_value (table_witness_sq p) x)
   (polynomial_value p x*polynomial_value p x).
Proof. apply table_fast_mul_value. Qed.
Lemma table_witness_cube_value p x :
 eqm feP (polynomial_value (table_witness_cube p) x)
   (polynomial_value p x*polynomial_value p x*polynomial_value p x).
Proof.
 unfold table_witness_cube;transitivity
   (polynomial_value (table_witness_sq p) x*polynomial_value p x).
 - apply table_fast_mul_value.
 - apply Zmult_eqm;[apply table_witness_sq_value|reflexivity].
Qed.

Lemma table_witness_h_value n x :
 eqm feP (polynomial_value (table_witness_h n) x)
   (table_numeric_h (polynomial_value (table_witness_x n) x)
    (polynomial_value (table_witness_d n) x) (polynomial_value table_witness_bx x)).
Proof.
 unfold table_witness_h;transitivity
  (polynomial_value table_witness_bx x*polynomial_value (table_witness_sq (table_witness_d n)) x-
    polynomial_value (table_witness_x n) x).
 - transitivity
    (polynomial_value (fast_polynomial_mul table_witness_bx (table_witness_sq (table_witness_d n))) x-
     polynomial_value (table_witness_x n) x).
   + apply table_fast_sub_value.
   + apply Zminus_eqm;[apply table_fast_mul_value|reflexivity].
 - setoid_rewrite (table_witness_sq_value (table_witness_d n) x);unfold table_numeric_h;ring.
Qed.
Lemma table_witness_i_value n x :
 eqm feP (polynomial_value (table_witness_i n) x)
   (table_numeric_i (polynomial_value (table_witness_y n) x)
    (polynomial_value (table_witness_d n) x) (polynomial_value table_witness_by x)).
Proof.
 unfold table_witness_i;transitivity
  (polynomial_value table_witness_by x*polynomial_value (table_witness_cube (table_witness_d n)) x-
    polynomial_value (table_witness_y n) x).
 - transitivity
    (polynomial_value (fast_polynomial_mul table_witness_by (table_witness_cube (table_witness_d n))) x-
     polynomial_value (table_witness_y n) x).
   + apply table_fast_sub_value.
   + apply Zminus_eqm;[apply table_fast_mul_value|reflexivity].
 - setoid_rewrite (table_witness_cube_value (table_witness_d n) x);unfold table_numeric_i;ring.
Qed.

Lemma table_witness_next_x_value n x :
 eqm feP (polynomial_value (table_witness_next_x n) x)
  (table_numeric_next_x (polynomial_value (table_witness_x n) x)
   (polynomial_value (table_witness_h n) x) (polynomial_value (table_witness_i n) x)).
Proof.
 unfold table_witness_next_x.
 transitivity ((polynomial_value (table_witness_i n) x*polynomial_value (table_witness_i n) x-
   polynomial_value (table_witness_h n) x*polynomial_value (table_witness_h n) x*polynomial_value (table_witness_h n) x)-
   2*(polynomial_value (table_witness_x n) x*
    (polynomial_value (table_witness_h n) x*polynomial_value (table_witness_h n) x))).
 - transitivity
    (polynomial_value (fast_polynomial_sub (table_witness_sq (table_witness_i n))
      (table_witness_cube (table_witness_h n))) x-
     polynomial_value (fast_polynomial_scale 2
      (fast_polynomial_mul (table_witness_x n) (table_witness_sq (table_witness_h n)))) x).
   + apply table_fast_sub_value.
   + apply Zminus_eqm.
     * transitivity (polynomial_value (table_witness_sq (table_witness_i n)) x-
         polynomial_value (table_witness_cube (table_witness_h n)) x).
       -- apply table_fast_sub_value.
       -- apply Zminus_eqm;[apply table_witness_sq_value|apply table_witness_cube_value].
     * transitivity (2*polynomial_value
         (fast_polynomial_mul (table_witness_x n) (table_witness_sq (table_witness_h n))) x).
       -- apply table_fast_scale_value.
       -- apply Zmult_eqm;[reflexivity|].
          transitivity (polynomial_value (table_witness_x n) x*
            polynomial_value (table_witness_sq (table_witness_h n)) x).
          ++ apply table_fast_mul_value.
          ++ apply Zmult_eqm;[reflexivity|apply table_witness_sq_value].
 - unfold table_numeric_next_x;ring.
Qed.
Lemma table_fast_mul_residue p q x a b :
 eqm feP (polynomial_value p x) a -> eqm feP (polynomial_value q x) b ->
 eqm feP (polynomial_value (fast_polynomial_mul p q) x) (a*b).
Proof.
 intros A B;transitivity (polynomial_value p x*polynomial_value q x).
 - apply table_fast_mul_value.
 - apply Zmult_eqm;assumption.
Qed.
Lemma table_fast_sub_residue p q x a b :
 eqm feP (polynomial_value p x) a -> eqm feP (polynomial_value q x) b ->
 eqm feP (polynomial_value (fast_polynomial_sub p q) x) (a-b).
Proof.
 intros A B;transitivity (polynomial_value p x-polynomial_value q x).
 - apply table_fast_sub_value.
 - apply Zminus_eqm;assumption.
Qed.
Lemma table_fast_scale_residue k p x a :
 eqm feP (polynomial_value p x) a ->
 eqm feP (polynomial_value (fast_polynomial_scale k p) x) (k*a).
Proof.
 intro A;transitivity (k*polynomial_value p x).
 - apply table_fast_scale_value.
 - apply Zmult_eqm;[reflexivity|exact A].
Qed.

Lemma table_witness_next_y_value n x :
 eqm feP (polynomial_value (table_witness_next_y n) x)
  (table_numeric_next_y (polynomial_value (table_witness_x n) x)
   (polynomial_value (table_witness_y n) x)
   (polynomial_value (table_witness_h n) x) (polynomial_value (table_witness_i n) x)).
Proof.
 unfold table_witness_next_y.
 transitivity
  (polynomial_value (table_witness_i n) x*
    (polynomial_value (table_witness_x n) x*
      (polynomial_value (table_witness_h n) x*polynomial_value (table_witness_h n) x)-
     table_numeric_next_x (polynomial_value (table_witness_x n) x)
      (polynomial_value (table_witness_h n) x) (polynomial_value (table_witness_i n) x))-
   polynomial_value (table_witness_y n) x*
    (polynomial_value (table_witness_h n) x*polynomial_value (table_witness_h n) x*polynomial_value (table_witness_h n) x)).
 - apply table_fast_sub_residue.
   + apply table_fast_mul_residue;[reflexivity|].
     apply table_fast_sub_residue.
     * apply table_fast_mul_residue;[reflexivity|apply table_witness_sq_value].
     * apply table_witness_next_x_value.
   + apply table_fast_mul_residue;[reflexivity|apply table_witness_cube_value].
 - unfold table_numeric_next_y;ring.
Qed.

Local Transparent polynomial_value.
Lemma table_polynomial_one_value x : eqm feP (polynomial_value (1::nil) x) 1.
Proof. cbn [polynomial_value];ring. Qed.
Lemma table_polynomial_x_value x : eqm feP (polynomial_value (0::1::nil) x) x.
Proof. cbn [polynomial_value];ring. Qed.
Lemma table_polynomial_xx_value x : eqm feP (polynomial_value (0::0::1::nil) x) (x*x).
Proof. cbn [polynomial_value];ring. Qed.
Lemma table_witness_s_value x : eqm feP (polynomial_value table_witness_s x) (table_curve_s x).
Proof. cbn [table_witness_s polynomial_value];unfold table_curve_s;ring. Qed.
Local Opaque polynomial_value.

Lemma table_witness_slope_value x :
 eqm feP (polynomial_value table_witness_slope x) (table_double_slope x).
Proof.
 unfold table_witness_slope.
 transitivity (((3*table_half) mod feP)*(x*x)).
 - apply table_fast_scale_residue;apply table_polynomial_xx_value.
 - setoid_rewrite (table_modulo_residue (3*table_half));unfold table_double_slope;ring.
Qed.
Lemma table_witness_bx_value x :
 eqm feP (polynomial_value table_witness_bx x) (table_double_x x).
Proof.
 unfold table_witness_bx.
 transitivity (table_double_slope x*table_double_slope x-2*(x*table_curve_s x)).
 - apply table_fast_sub_residue.
   + unfold table_witness_sq;apply table_fast_mul_residue;apply table_witness_slope_value.
   + apply table_fast_scale_residue;apply table_fast_mul_residue.
     * apply table_polynomial_x_value.
     * apply table_witness_s_value.
 - unfold table_double_x;ring.
Qed.
Lemma table_witness_by_value x :
 eqm feP (polynomial_value table_witness_by x) (table_double_y x).
Proof.
 unfold table_witness_by.
 transitivity (table_double_slope x*(3*(x*table_curve_s x)-table_double_slope x*table_double_slope x)-
   table_curve_s x*table_curve_s x).
 - apply table_fast_sub_residue.
   + apply table_fast_mul_residue;[apply table_witness_slope_value|].
     apply table_fast_sub_residue.
     * apply table_fast_scale_residue;apply table_fast_mul_residue.
       -- apply table_polynomial_x_value.
       -- apply table_witness_s_value.
     * unfold table_witness_sq;apply table_fast_mul_residue;apply table_witness_slope_value.
   + unfold table_witness_sq;apply table_fast_mul_residue;apply table_witness_s_value.
 - unfold table_double_y;ring.
Qed.
Lemma table_witness_seed_values x :
 eqm feP (polynomial_value (table_witness_x 1) x) (x*table_curve_s x) /\
 eqm feP (polynomial_value (table_witness_y 1) x) (table_curve_s x*table_curve_s x) /\
 eqm feP (polynomial_value (table_witness_d 1) x) 1.
Proof.
 split.
 - change (eqm feP (polynomial_value (fast_polynomial_mul table_witness_s (0::1::nil)) x)
     (x*table_curve_s x)).
   transitivity (table_curve_s x*x).
   + apply table_fast_mul_residue;[apply table_witness_s_value|apply table_polynomial_x_value].
   + ring.
 - split.
   + change (eqm feP (polynomial_value (fast_polynomial_mul (table_witness_sq table_witness_s) (1::nil)) x)
       (table_curve_s x*table_curve_s x)).
     transitivity ((table_curve_s x*table_curve_s x)*1).
     * apply table_fast_mul_residue.
       -- unfold table_witness_sq;apply table_fast_mul_residue;apply table_witness_s_value.
       -- apply table_polynomial_one_value.
     * ring.
   + apply table_polynomial_one_value.
Qed.
Lemma table_numeric_next_x_respects x h i hh ii :
 eqm feP h hh -> eqm feP i ii ->
 eqm feP (table_numeric_next_x x h i) (table_numeric_next_x x hh ii).
Proof.
 intros HRes IRes;unfold table_numeric_next_x;setoid_rewrite HRes;setoid_rewrite IRes;reflexivity.
Qed.
Lemma table_numeric_next_y_respects x y h i hh ii :
 eqm feP h hh -> eqm feP i ii ->
 eqm feP (table_numeric_next_y x y h i) (table_numeric_next_y x y hh ii).
Proof.
 intros HRes IRes;unfold table_numeric_next_y,table_numeric_next_x.
 setoid_rewrite HRes;setoid_rewrite IRes;reflexivity.
Qed.
Local Opaque table_witness_h table_witness_i table_witness_next_x table_witness_next_y
 table_witness_x table_witness_y table_witness_d table_witness_bx table_witness_by table_witness_f.
Theorem table_witness_step_values n x :
 table_witness_step n=table_witness_scaled_next n ->
 let px:=polynomial_value (table_witness_x n) x in
 let py:=polynomial_value (table_witness_y n) x in
 let pz:=polynomial_value (table_witness_d n) x in
 let h:=table_numeric_h px pz (polynomial_value table_witness_bx x) in
 let i:=table_numeric_i py pz (polynomial_value table_witness_by x) in
 let f:=polynomial_value (table_witness_f n) x in
 eqm feP (table_numeric_next_x px h i) (f*f*polynomial_value (table_witness_x (n+2)%nat) x) /\
 eqm feP (table_numeric_next_y px py h i) (f*f*f*polynomial_value (table_witness_y (n+2)%nat) x) /\
 eqm feP (pz*h) (f*polynomial_value (table_witness_d (n+2)%nat) x).
Proof.
 intro Coefficients;cbn zeta.
 pose proof (f_equal (fun q=>snd (fst (fst q))) Coefficients) as XPolynomial.
 pose proof (f_equal (fun q=>snd (fst q)) Coefficients) as YPolynomial.
 pose proof (f_equal snd Coefficients) as ZPolynomial.
 cbn [table_witness_step table_witness_scaled_next fst snd] in XPolynomial,YPolynomial,ZPolynomial.
 assert (NX:eqm feP (polynomial_value (table_witness_next_x n) x)
   (table_numeric_next_x (polynomial_value (table_witness_x n) x)
    (table_numeric_h (polynomial_value (table_witness_x n) x) (polynomial_value (table_witness_d n) x)
      (polynomial_value table_witness_bx x))
    (table_numeric_i (polynomial_value (table_witness_y n) x) (polynomial_value (table_witness_d n) x)
      (polynomial_value table_witness_by x)))).
 { transitivity (table_numeric_next_x (polynomial_value (table_witness_x n) x)
     (polynomial_value (table_witness_h n) x) (polynomial_value (table_witness_i n) x)).
   - apply table_witness_next_x_value.
   - apply table_numeric_next_x_respects;[apply table_witness_h_value|apply table_witness_i_value]. }
 assert (NY:eqm feP (polynomial_value (table_witness_next_y n) x)
   (table_numeric_next_y (polynomial_value (table_witness_x n) x) (polynomial_value (table_witness_y n) x)
    (table_numeric_h (polynomial_value (table_witness_x n) x) (polynomial_value (table_witness_d n) x)
      (polynomial_value table_witness_bx x))
    (table_numeric_i (polynomial_value (table_witness_y n) x) (polynomial_value (table_witness_d n) x)
      (polynomial_value table_witness_by x)))).
 { transitivity (table_numeric_next_y (polynomial_value (table_witness_x n) x)
     (polynomial_value (table_witness_y n) x)
     (polynomial_value (table_witness_h n) x) (polynomial_value (table_witness_i n) x)).
   - apply table_witness_next_y_value.
   - apply table_numeric_next_y_respects;[apply table_witness_h_value|apply table_witness_i_value]. }
 split.
 - transitivity (polynomial_value (table_witness_next_x n) x);[symmetry;exact NX|].
   rewrite XPolynomial.
   transitivity (polynomial_value (table_witness_sq (table_witness_f n)) x*
     polynomial_value (table_witness_x (n+2)%nat) x).
   + apply table_fast_mul_value.
   + apply Zmult_eqm;[apply table_witness_sq_value|reflexivity].
 - split.
   + transitivity (polynomial_value (table_witness_next_y n) x);[symmetry;exact NY|].
     rewrite YPolynomial.
     transitivity (polynomial_value (table_witness_cube (table_witness_f n)) x*
       polynomial_value (table_witness_y (n+2)%nat) x).
     * apply table_fast_mul_value.
     * apply Zmult_eqm;[apply table_witness_cube_value|reflexivity].
   + transitivity (polynomial_value (table_witness_d n) x*polynomial_value (table_witness_h n) x).
     * apply Zmult_eqm;[reflexivity|symmetry;apply table_witness_h_value].
     * transitivity (polynomial_value (fast_polynomial_mul (table_witness_d n) (table_witness_h n)) x).
       -- symmetry;apply table_fast_mul_value.
       -- rewrite ZPolynomial;apply table_fast_mul_value.
Qed.
End TableCoordinateValues.

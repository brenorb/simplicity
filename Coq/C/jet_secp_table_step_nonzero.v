(** Transfer the checked coefficient factorizations to nonzero step factors.
    Coefficient equality is supplied by the individual closed certificates;
    the curve equation discharges every root-exclusion condition. *)
From Coq Require Import ZArith Znumtheory List Lia Ring Morphisms Setoid.
Require Import C.jet_secp_fe_math C.jet_secp_polynomial C.jet_secp_fast_polynomial
 C.jet_secp_field_prime C.jet_secp_table_coordinates C.jet_secp_table_coordinate_values
 C.jet_secp_table_affine_seed.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque polynomial_value.
Definition table_step_indices : list nat := [1%nat;3%nat;5%nat;7%nat;9%nat;11%nat;13%nat].
Definition table_odd_indices : list nat := [1%nat;3%nat;5%nat;7%nat;9%nat;11%nat;13%nat;15%nat].
Definition table_previous_value n x :=
 if Nat.eqb n 1 then feP-1 else polynomial_value (table_witness_d (n-2)%nat) x.
Section TableStepNonzero.
Local Lemma table_nonzero_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_nonzero_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_nonzero_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_nonzero_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_nonzero_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_nonzero_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_nonzero_modring : table_nonzero_ring (constants [Zcst]).

Lemma table_step_index_members n : In n table_step_indices ->
 In n table_odd_indices /\ In (n+2)%nat table_odd_indices /\
 (n=1%nat \/ In (n-2)%nat table_odd_indices).
Proof.
 unfold table_step_indices;intro Member.
 repeat (destruct Member as [Equal|Member];[subst n;cbn [table_odd_indices In];intuition|]).
 contradiction.
Qed.
Local Transparent polynomial_value.
Lemma table_previous_value_polynomial n x :
 eqm feP (polynomial_value (if Nat.eqb n 1 then [feP-1] else table_witness_d (n-2)%nat) x)
  (table_previous_value n x).
Proof.
 unfold table_previous_value;destruct (Nat.eqb n 1);[cbn [polynomial_value];ring|reflexivity].
Qed.
Local Opaque polynomial_value.

Lemma table_witness_f_value n x :
 eqm feP (polynomial_value (table_witness_f n) x)
  (table_half*table_half*polynomial_value (table_witness_d n) x*table_previous_value n x).
Proof.
 unfold table_witness_f.
 transitivity (((table_half*table_half) mod feP)*
   (polynomial_value (table_witness_d n) x*table_previous_value n x)).
 - apply table_fast_scale_residue;apply table_fast_mul_residue;
     [reflexivity|apply table_previous_value_polynomial].
 - setoid_rewrite (table_modulo_residue (table_half*table_half));ring.
Qed.
Lemma table_witness_h_factor n x :
 table_witness_step n=table_witness_scaled_next n ->
 eqm feP (polynomial_value (table_witness_h n) x)
  (table_half*table_half*polynomial_value (table_witness_d (n+2)%nat) x*table_previous_value n x).
Proof.
 intro Coefficients.
 pose proof (f_equal (fun q=>fst (fst (fst q))) Coefficients) as HPolynomial.
 cbn [table_witness_step table_witness_scaled_next fst snd] in HPolynomial.
 rewrite HPolynomial.
 transitivity (((table_half*table_half) mod feP)*
   (polynomial_value (table_witness_d (n+2)%nat) x*table_previous_value n x)).
 - apply table_fast_scale_residue;apply table_fast_mul_residue;
     [reflexivity|apply table_previous_value_polynomial].
 - setoid_rewrite (table_modulo_residue (table_half*table_half));ring.
Qed.
Lemma table_previous_nonzero n x y :
 In n table_step_indices -> (x*x*x+7) mod feP=(y*y) mod feP ->
 table_previous_value n x mod feP<>0.
Proof.
 intros Member Curve;destruct (table_step_index_members n Member) as (_ & _ & Previous).
 unfold table_previous_value;destruct (Nat.eqb n 1) eqn:IsOne.
 - vm_compute;discriminate.
 - destruct Previous as [Equal|Previous].
   + subst n;discriminate IsOne.
   + apply (table_witness_d_nonzero _ x y Previous Curve).
Qed.
Lemma table_half_square_nonzero : (table_half*table_half) mod feP<>0.
Proof. unfold table_half;vm_compute;discriminate. Qed.
Theorem table_witness_f_nonzero n x y :
 In n table_step_indices -> (x*x*x+7) mod feP=(y*y) mod feP ->
 polynomial_value (table_witness_f n) x mod feP<>0.
Proof.
 intros Member Curve;pose proof (table_witness_f_value n x) as Factor;unfold eqm in Factor.
 rewrite Factor;apply secp256k1_nonzero_product.
 - apply secp256k1_nonzero_product;[exact table_half_square_nonzero|].
   apply (table_witness_d_nonzero n x y (proj1 (table_step_index_members n Member)) Curve).
 - exact (table_previous_nonzero n x y Member Curve).
Qed.
Theorem table_witness_h_nonzero n x y :
 In n table_step_indices -> (x*x*x+7) mod feP=(y*y) mod feP ->
 table_witness_step n=table_witness_scaled_next n ->
 polynomial_value (table_witness_h n) x mod feP<>0.
Proof.
 intros Member Curve Coefficients.
 pose proof (table_witness_h_factor n x Coefficients) as Factor;unfold eqm in Factor.
 rewrite Factor;apply secp256k1_nonzero_product.
 - apply secp256k1_nonzero_product;[exact table_half_square_nonzero|].
   apply (table_witness_d_nonzero _ x y (proj1 (proj2 (table_step_index_members n Member))) Curve).
 - exact (table_previous_nonzero n x y Member Curve).
Qed.
End TableStepNonzero.

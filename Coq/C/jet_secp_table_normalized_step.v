(** One original literal table step from a scaled coefficient witness.
    The curve equation and checked coefficient equality derive both branch
    conditions; no nonzero-H or nonzero-Z hypothesis is added to the input. *)
From Coq Require Import ZArith Znumtheory List Lia Ring Morphisms Setoid.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_polynomial
 C.jet_secp_table_coordinates C.jet_secp_table_coordinate_values C.jet_secp_table_step_nonzero
 C.jet_secp_table_scaled_step C.jet_secp_table_affine_first C.jet_secp_curve_literal
 C.jet_secp_canonical_zero C.jet_secp_add_literal C.jet_secp_mixed_dispatch_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque polynomial_value toZ table_witness_d table_witness_x table_witness_y
 table_witness_bx table_witness_by table_witness_f mixed_literal_h.
Definition table_point_residue n x k
 (p:Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) :=
 eqm feP (@toZ (WordToZ 8) (fst (fst p))) (k*k*polynomial_value (table_witness_x n) x) /\
 eqm feP (@toZ (WordToZ 8) (snd (fst p))) (k*k*k*polynomial_value (table_witness_y n) x) /\
 eqm feP (@toZ (WordToZ 8) (snd p)) (k*polynomial_value (table_witness_d n) x).
Definition table_increment_residue x (p:Ty.tySem (Ty.Prod (Word 8) (Word 8))) :=
 eqm feP (@toZ (WordToZ 8) (fst p)) (polynomial_value table_witness_bx x) /\
 eqm feP (@toZ (WordToZ 8) (snd p)) (polynomial_value table_witness_by x).
Lemma table_nonzero_opposite a : a mod feP<>0 -> (-a) mod feP<>0.
Proof.
 intro Nonzero;pose proof (secp256k1_nonzero_product (-1) a ltac:(vm_compute;discriminate) Nonzero) as Product.
 replace ((-1)*a) with (-a) in Product by lia;exact Product.
Qed.
Lemma table_point_residue_finite n x y k p :
 In n table_odd_indices -> (x*x*x+7) mod feP=(y*y) mod feP ->
 k mod feP<>0 -> table_point_residue n x k p ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (snd p))=false.
Proof.
 intros Member Curve Scale (_ & _ & ZResidue).
 rewrite literal_curve_zero_numeric;apply Z.eqb_neq;unfold eqm in ZResidue;rewrite ZResidue.
 apply secp256k1_nonzero_product;[exact Scale|exact (table_witness_d_nonzero n x y Member Curve)].
Qed.
Section TableNormalizedStep.
Local Lemma table_normalized_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_normalized_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_normalized_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_normalized_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_normalized_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_normalized_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_normalized_modring : table_normalized_ring (constants [Zcst]).

Theorem literal_table_normalized_step n x y k p increment :
 In n table_step_indices -> (x*x*x+7) mod feP=(y*y) mod feP ->
 table_witness_step n=table_witness_scaled_next n ->
 k mod feP<>0 -> table_point_residue n x k p -> table_increment_residue x increment ->
 let next_scale:=k*k*k*polynomial_value (table_witness_f n) x in
 next_scale mod feP<>0 /\
 table_point_residue (n+2)%nat x next_scale
  (snd (@literal_gej_ge_add_ex Alg.CoreFunSem (p,increment))).
Proof.
 intros Member Curve Coefficients Scale Representation Increment;cbn zeta.
 destruct p as [[ax ay] az];destruct increment as [bx byword].
 pose proof (table_point_residue_finite n x y k ((ax,ay),az)
   (proj1 (table_step_index_members n Member)) Curve Scale Representation) as NonzeroZ.
 destruct Representation as (AX & AY & AZ);destruct Increment as [BX BY].
 cbn [fst snd] in AX,AY,AZ,BX,BY,NonzeroZ.
 assert (HResidue:eqm feP (@toZ (WordToZ 8) (mixed_literal_h ax az bx))
   (-(k*k*polynomial_value (table_witness_h n) x))).
 { transitivity (-table_numeric_h (k*k*polynomial_value (table_witness_x n) x)
     (k*polynomial_value (table_witness_d n) x) (polynomial_value table_witness_bx x)).
   - apply literal_table_h_residue;assumption.
   - transitivity (-(k*k*table_numeric_h (polynomial_value (table_witness_x n) x)
       (polynomial_value (table_witness_d n) x) (polynomial_value table_witness_bx x))).
     + unfold table_numeric_h;ring.
     + apply Zopp_eqm;apply Zmult_eqm;[reflexivity|symmetry;apply table_witness_h_value]. }
 assert (NonzeroH:Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx))=false).
 { rewrite literal_curve_zero_numeric;apply Z.eqb_neq;unfold eqm in HResidue;rewrite HResidue.
   apply table_nonzero_opposite;apply secp256k1_nonzero_product.
   - apply secp256k1_nonzero_product;assumption.
   - exact (table_witness_h_nonzero n x y Member Curve Coefficients). }
 destruct (literal_table_mixed_scaled ax ay az bx byword k
   (polynomial_value (table_witness_x n) x) (polynomial_value (table_witness_y n) x)
   (polynomial_value (table_witness_d n) x)
   (polynomial_value table_witness_bx x) (polynomial_value table_witness_by x)
   AX AY AZ BX BY NonzeroZ NonzeroH) as (XResult & YResult & ZResult).
 destruct (table_witness_step_values n x Coefficients) as (XValue & YValue & ZValue).
 split.
 - apply secp256k1_nonzero_product.
   + apply secp256k1_nonzero_product;[apply secp256k1_nonzero_product|];assumption.
   + exact (table_witness_f_nonzero n x y Member Curve).
 - rewrite literal_table_mixed_point_projection;unfold table_point_residue.
   split.
   + eapply eqm_trans;[exact XResult|].
     transitivity ((k*k*k)*(k*k*k)*
       (polynomial_value (table_witness_f n) x*polynomial_value (table_witness_f n) x*
        polynomial_value (table_witness_x (n+2)%nat) x)).
     * apply Zmult_eqm;[reflexivity|exact XValue].
     * ring.
   + split.
     * eapply eqm_trans;[exact YResult|].
       transitivity ((k*k*k)*(k*k*k)*(k*k*k)*
         (polynomial_value (table_witness_f n) x*polynomial_value (table_witness_f n) x*
          polynomial_value (table_witness_f n) x*polynomial_value (table_witness_y (n+2)%nat) x)).
       -- apply Zmult_eqm;[reflexivity|exact YValue].
       -- ring.
     * eapply eqm_trans;[exact ZResult|].
       transitivity (k*k*k*(polynomial_value (table_witness_f n) x*
         polynomial_value (table_witness_d (n+2)%nat) x)).
       -- apply Zmult_eqm;[reflexivity|exact ZValue].
       -- ring.
Qed.
End TableNormalizedStep.

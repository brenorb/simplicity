(** The shared denominator of the original scalarTable5 is nonzero for
    every valid affine input at Z=1. This discharges an internal premise
    of the whole ecmult flag theorem without restricting the public input. *)
From Coq Require Import ZArith Znumtheory List Lia Ring Morphisms Setoid.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_polynomial
 C.jet_secp_table_coordinates C.jet_secp_table_coordinate_values C.jet_secp_table_step_nonzero
 C.jet_secp_table_step_certificates C.jet_secp_table_normalized_step
 C.jet_secp_table_affine_seed C.jet_secp_curve_literal C.jet_secp_canonical_zero
 C.jet_secp_add_literal C.jet_secp_rescale_literal C.jet_secp_double_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_multiply_literal_spec
 C.jet_secp_negate_literal_contract C.jet_secp_scalar_table_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque polynomial_value toZ literal_gej_double literal_gej_zinv literal_fe_multiply
 literal_fe_one256 literal_pass1_8 literal_pass2_8 table_witness_d table_witness_x table_witness_y.
Fixpoint table_walk_scale (j:nat) (x:Z) : Z :=
 match j with Datatypes.O=>1 | Datatypes.S previous=>let k:=table_walk_scale previous x in
  k*k*k*polynomial_value (table_witness_f (2*previous+1)%nat) x end.
Lemma table_walk_step_index j : (j<7)%nat -> In (2*j+1)%nat table_step_indices.
Proof. unfold table_step_indices;cbn [In];lia. Qed.
Theorem literal_table_walk_residue j x y start increment :
 (j<=7)%nat -> (x*x*x+7) mod feP=(y*y) mod feP ->
 table_point_residue 1 x 1 start -> table_increment_residue x increment ->
 table_walk_scale j x mod feP<>0 /\
 table_point_residue (2*j+1)%nat x (table_walk_scale j x)
   (literal_table_advance j start increment).
Proof.
 intros Range Curve Start Increment;induction j as [|j IH].
 - split;[vm_compute;discriminate|exact Start].
 - destruct (IH ltac:(lia)) as [Scale Representation].
   pose proof (table_walk_step_index j ltac:(lia)) as Member.
   pose proof (literal_table_normalized_step (2*j+1)%nat x y (table_walk_scale j x)
     (literal_table_advance j start increment) increment Member Curve
     (table_witness_step_checked _ Member) Scale Representation Increment) as Next.
   cbn zeta in Next.
   change ((table_walk_scale j x*table_walk_scale j x*table_walk_scale j x*
       polynomial_value (table_witness_f (2*j+1)%nat) x) mod feP<>0 /\
     table_point_residue (2*Datatypes.S j+1)%nat x
      (table_walk_scale j x*table_walk_scale j x*table_walk_scale j x*
       polynomial_value (table_witness_f (2*j+1)%nat) x)
      (snd (@literal_gej_ge_add_ex Alg.CoreFunSem (literal_table_advance j start increment,increment)))).
   replace (2*Datatypes.S j+1)%nat with ((2*j+1)+2)%nat by lia;exact Next.
Qed.

Local Opaque table_walk_scale literal_table_advance literal_gej_ge_add_ex.
Lemma literal_table_pass1_last (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge) :
 snd (@literal_pass1_8 Alg.CoreFunSem (a,b))=snd (literal_table_advance 7 a b).
Proof.
 (* Project with a match so conversion discards the unused ratio tree. *)
 pose proof (literal_pass1_8_step a b) as Step.
 lazymatch type of Step with
 | @eq ?A ?lhs ?rhs =>
   pose proof (@f_equal A (Ty.tySem (Word 8))
     (fun q:Ty.tySem (Ty.Prod (literal_table_tree 3) (Word 8))=>
       match q with (_,last)=>last end) lhs rhs Step) as Projected
 end.
 cbn [snd] in Projected;exact Projected.
Qed.
Section AffineSeedResidue.
Local Lemma table_affine_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_affine_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_affine_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_affine_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_affine_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_affine_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_affine_modring : table_affine_ring (constants [Zcst]).

Lemma literal_table_seed_residue (ax ay:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true ->
 let d:=@literal_gej_double Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d) in
 table_point_residue 1 (@toZ (WordToZ 8) ax) 1 (seed,@literal_fe_one256 Alg.CoreFunSem tt) /\
 table_increment_residue (@toZ (WordToZ 8) ax) (fst d).
Proof.
 intro Valid;cbn zeta.
 destruct (literal_table_affine_seed ax ay Valid) as (SX & SY & NonzeroD).
 destruct (literal_table_affine_double ax ay Valid) as (DX & DY & DZ).
 destruct (table_witness_seed_values (@toZ (WordToZ 8) ax)) as (WX & WY & WZ).
 unfold table_point_residue,table_increment_residue;cbn [fst snd].
 split.
 - split.
   + transitivity (@toZ (WordToZ 8) ax*table_curve_s (@toZ (WordToZ 8) ax));[exact SX|].
     transitivity (polynomial_value (table_witness_x 1) (@toZ (WordToZ 8) ax));[symmetry;exact WX|ring].
   + split.
     * transitivity (table_curve_s (@toZ (WordToZ 8) ax)*table_curve_s (@toZ (WordToZ 8) ax));[exact SY|].
       transitivity (polynomial_value (table_witness_y 1) (@toZ (WordToZ 8) ax));[symmetry;exact WY|ring].
     * rewrite literal_fe_one256_value;transitivity 1;[reflexivity|].
       transitivity (polynomial_value (table_witness_d 1) (@toZ (WordToZ 8) ax));[symmetry;exact WZ|ring].
 - split.
   + transitivity (table_double_x (@toZ (WordToZ 8) ax));[exact DX|symmetry;apply table_witness_bx_value].
   + transitivity (table_double_y (@toZ (WordToZ 8) ax));[exact DY|symmetry;apply table_witness_by_value].
Qed.
End AffineSeedResidue.

Theorem literal_affine_scalar_table_nonzero (ax ay:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
  (fst (@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt))))=false.
Proof.
 intro Valid.
 pose proof (literal_table_affine_curve ax ay Valid) as Curve.
 destruct (literal_table_affine_seed ax ay Valid) as (_ & _ & NonzeroD).
 destruct (literal_table_seed_residue ax ay Valid) as [Start Increment].
 destruct (literal_table_walk_residue 7 (@toZ (WordToZ 8) ax) (@toZ (WordToZ 8) ay) _ _
   ltac:(lia) Curve Start Increment) as [Scale Representation].
 pose proof (table_point_residue_finite 15 (@toZ (WordToZ 8) ax) (@toZ (WordToZ 8) ay) _ _
   ltac:(unfold table_odd_indices;do 7 right;left;reflexivity) Curve Scale Representation) as NonzeroLast.
 set (d:=@literal_gej_double Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)) in *.
 set (seed:=@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d)) in *.
 assert (Route:fst (@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt))=
   @literal_fe_multiply Alg.CoreFunSem (snd d,
    snd (literal_table_advance 7 (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d)))).
 { change (@literal_fe_multiply Alg.CoreFunSem (snd d,
     snd (@literal_pass1_8 Alg.CoreFunSem ((seed,@literal_fe_one256 Alg.CoreFunSem tt),fst d)))=
    @literal_fe_multiply Alg.CoreFunSem (snd d,
     snd (literal_table_advance 7 (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d)))).
   apply (f_equal (fun z=>@literal_fe_multiply Alg.CoreFunSem (snd d,z))).
   apply literal_table_pass1_last. }
 pose proof (f_equal (fun w=>Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem w)) Route) as Observed.
 eapply eq_trans;[exact Observed|].
 rewrite literal_curve_zero_numeric,literal_multiply_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply Z.eqb_neq;apply secp256k1_nonzero_product;
   apply Z.eqb_neq;rewrite <-literal_curve_zero_numeric;assumption.
Qed.

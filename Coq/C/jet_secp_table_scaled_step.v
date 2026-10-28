(** Residue semantics of the original nonzero-H mixed-addition branch.
    These intermediate conditions are discharged by the table certificates;
    they are not additional preconditions for a public jet. *)
From Coq Require Import ZArith Znumtheory Ring Morphisms Setoid.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_table_affine_seed
 C.jet_secp_table_affine_first C.jet_secp_curve_literal C.jet_secp_rescale_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_canonical_zero
 C.jet_secp_multiply_literal_spec C.jet_secp_mixed_dispatch_literal
 C.jet_secp_mixed_nonzero_literal C.jet_secp_generator_point_numeric C.jet_secp_add_literal
 C.jet_secp_negate_literal_contract C.jet_secp_double_literal C.jet_secp_square_execution.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque toZ literal_fe_multiply literal_fe_add literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int literal_fe_one256 mixed_literal_h mixed_literal_i
 mixed_literal_rx.
Definition table_numeric_h x z bx := bx*z*z-x.
Definition table_numeric_i y z byword := byword*z*z*z-y.
Definition table_numeric_next_x x h i := i*i-h*h*h-2*x*h*h.
Definition table_numeric_next_y x y h i := i*(x*h*h-table_numeric_next_x x h i)-y*h*h*h.
Section TableMixedAlgebra.
Local Lemma table_mixed_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
 reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
 transitivity proved by (eqm_trans feP) as table_mixed_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_mixed_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_mixed_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP) as table_mixed_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as table_mixed_opp.
Proof. exact (Zopp_eqm feP). Qed.
Add Ring table_mixed_modring : table_mixed_ring (constants [Zcst]).

Lemma literal_table_cube_residue (a:Ty.tySem (Word 8)) u :
 eqm feP (@toZ (WordToZ 8) a) u ->
 eqm feP (@toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem a)) (u*u*u).
Proof.
 intro A;rewrite literal_curve_cube_numeric.
 transitivity (@toZ (WordToZ 8) a*@toZ (WordToZ 8) a*@toZ (WordToZ 8) a).
 - apply table_modulo_residue.
 - apply Zmult_eqm;[apply Zmult_eqm|];assumption.
Qed.
Lemma literal_table_h_residue (a z b:Ty.tySem (Word 8)) va vz vb :
 eqm feP (@toZ (WordToZ 8) a) va -> eqm feP (@toZ (WordToZ 8) z) vz ->
 eqm feP (@toZ (WordToZ 8) b) vb ->
 eqm feP (@toZ (WordToZ 8) (mixed_literal_h a z b)) (-table_numeric_h va vz vb).
Proof.
 intros A Z B;rewrite mixed_literal_h_numeric.
 transitivity (@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z).
 - apply table_modulo_residue.
 - transitivity (va-vb*vz*vz).
   + apply Zminus_eqm;[exact A|apply Zmult_eqm;[apply Zmult_eqm|];assumption].
   + unfold table_numeric_h;ring.
Qed.
Lemma literal_table_i_residue (a z b:Ty.tySem (Word 8)) va vz vb :
 eqm feP (@toZ (WordToZ 8) a) va -> eqm feP (@toZ (WordToZ 8) z) vz ->
 eqm feP (@toZ (WordToZ 8) b) vb ->
 eqm feP (@toZ (WordToZ 8) (mixed_literal_i a z b)) (-table_numeric_i va vz vb).
Proof.
 intros A Z B;rewrite mixed_literal_i_numeric.
 transitivity (@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z).
 - apply table_modulo_residue.
 - transitivity (va-vb*vz*vz*vz).
   + apply Zminus_eqm;[exact A|].
     apply Zmult_eqm;[|exact Z].
     apply Zmult_eqm;[|exact Z].
     apply Zmult_eqm;assumption.
   + unfold table_numeric_i;ring.
Qed.

Theorem literal_table_mixed_residues (ax ay az bx byword:Ty.tySem (Word 8)) x y z qx qy :
 eqm feP (@toZ (WordToZ 8) ax) x -> eqm feP (@toZ (WordToZ 8) ay) y ->
 eqm feP (@toZ (WordToZ 8) az) z -> eqm feP (@toZ (WordToZ 8) bx) qx ->
 eqm feP (@toZ (WordToZ 8) byword) qy ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx))=false ->
 let result:=@literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)) in
 let h:=table_numeric_h x z qx in let i:=table_numeric_i y z qy in
 eqm feP (@toZ (WordToZ 8) (fst (fst result))) (table_numeric_next_x x h i) /\
 eqm feP (@toZ (WordToZ 8) (snd (fst result))) (table_numeric_next_y x y h i) /\
 eqm feP (@toZ (WordToZ 8) (snd result)) (z*h).
Proof.
 intros AX AY AZ BX BY NonzeroZ NonzeroH;cbn zeta.
 rewrite literal_mixed_step;cbn zeta;rewrite NonzeroZ,NonzeroH;cbn [fst snd].
 set (h:=mixed_literal_h ax az bx).
 set (i:=mixed_literal_i ay az byword).
 set (u:=@literal_fe_multiply Alg.CoreFunSem (ax,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 set (v:=@literal_fe_multiply Alg.CoreFunSem (ay,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 set (hv:=table_numeric_h x z qx).
 set (iv:=table_numeric_i y z qy).
 assert (HRes:eqm feP (@toZ (WordToZ 8) h) (-hv)) by (apply literal_table_h_residue;assumption).
 assert (IRes:eqm feP (@toZ (WordToZ 8) i) (-iv)) by (apply literal_table_i_residue;assumption).
 assert (URes:eqm feP (@toZ (WordToZ 8) u) x).
 { unfold u;transitivity (x*(1*1));[apply literal_table_mul_residue|ring].
   - exact AX.
   - apply literal_table_square_residue;rewrite literal_fe_one256_value;reflexivity. }
 assert (VRes:eqm feP (@toZ (WordToZ 8) v) y).
 { unfold v;transitivity (y*(1*1*1));[apply literal_table_mul_residue|ring].
   - exact AY.
   - apply literal_table_cube_residue;rewrite literal_fe_one256_value;reflexivity. }
 assert (XRes:eqm feP (@toZ (WordToZ 8) (mixed_literal_rx h i u)) (table_numeric_next_x x hv iv)).
 { rewrite mixed_literal_rx_numeric.
   transitivity (@toZ (WordToZ 8) i*@toZ (WordToZ 8) i+
    @toZ (WordToZ 8) h*@toZ (WordToZ 8) h*@toZ (WordToZ 8) h+
    2*(-(@toZ (WordToZ 8) u*@toZ (WordToZ 8) h*@toZ (WordToZ 8) h))).
   - apply table_modulo_residue.
   - setoid_rewrite HRes;setoid_rewrite IRes;setoid_rewrite URes;unfold table_numeric_next_x;ring. }
 assert (TRes:eqm feP (@toZ (WordToZ 8) (mixed_literal_t h u)) (hv*hv*x)).
 { unfold mixed_literal_t;transitivity (((-hv)*(-hv))*x).
   - apply literal_table_mul_residue;[apply literal_table_square_residue;exact HRes|exact URes].
   - ring. }
 assert (GRes:eqm feP (@toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem h)) (-(hv*hv*hv))).
 { transitivity ((-hv)*(-hv)*(-hv));[apply literal_table_cube_residue;exact HRes|ring]. }
 split;[exact XRes|];split.
 - unfold mixed_literal_ry,mixed_literal_tx.
   transitivity ((-(hv*hv*hv))*y+(-iv)*(table_numeric_next_x x hv iv+(-(hv*hv*x)))).
   + apply literal_table_add_residue.
     * apply literal_table_mul_residue;[exact GRes|exact VRes].
     * apply literal_table_mul_residue;[exact IRes|].
       apply literal_table_add_residue;[exact XRes|apply literal_table_negate_residue;exact TRes].
   + unfold table_numeric_next_y;ring.
 - unfold mixed_literal_rz;transitivity (((-hv)*z)*(-1)).
   + apply literal_table_mul_residue.
     * apply literal_table_mul_residue;assumption.
     * apply (literal_table_negate_residue _ 1);rewrite literal_fe_one256_value;reflexivity.
   + ring.
Qed.
Theorem literal_table_mixed_scaled (ax ay az bx byword:Ty.tySem (Word 8)) k x y z qx qy :
 eqm feP (@toZ (WordToZ 8) ax) (k*k*x) ->
 eqm feP (@toZ (WordToZ 8) ay) (k*k*k*y) ->
 eqm feP (@toZ (WordToZ 8) az) (k*z) ->
 eqm feP (@toZ (WordToZ 8) bx) qx -> eqm feP (@toZ (WordToZ 8) byword) qy ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx))=false ->
 let result:=@literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)) in
 let h:=table_numeric_h x z qx in let i:=table_numeric_i y z qy in
 eqm feP (@toZ (WordToZ 8) (fst (fst result)))
   ((k*k*k)*(k*k*k)*table_numeric_next_x x h i) /\
 eqm feP (@toZ (WordToZ 8) (snd (fst result)))
   ((k*k*k)*(k*k*k)*(k*k*k)*table_numeric_next_y x y h i) /\
 eqm feP (@toZ (WordToZ 8) (snd result)) (k*k*k*(z*h)).
Proof.
 intros AX AY AZ BX BY NonzeroZ NonzeroH;cbn zeta.
 destruct (literal_table_mixed_residues ax ay az bx byword (k*k*x) (k*k*k*y) (k*z) qx qy
   AX AY AZ BX BY NonzeroZ NonzeroH) as (XRes & YRes & ZRes).
 assert (HScale:eqm feP (table_numeric_h (k*k*x) (k*z) qx) (k*k*table_numeric_h x z qx))
   by (unfold table_numeric_h;ring).
 assert (IScale:eqm feP (table_numeric_i (k*k*k*y) (k*z) qy) (k*k*k*table_numeric_i y z qy))
   by (unfold table_numeric_i;ring).
 split.
 - transitivity (table_numeric_next_x (k*k*x) (table_numeric_h (k*k*x) (k*z) qx)
     (table_numeric_i (k*k*k*y) (k*z) qy));[exact XRes|].
   unfold table_numeric_next_x;setoid_rewrite HScale;setoid_rewrite IScale;ring.
 - split.
   + transitivity (table_numeric_next_y (k*k*x) (k*k*k*y) (table_numeric_h (k*k*x) (k*z) qx)
       (table_numeric_i (k*k*k*y) (k*z) qy));[exact YRes|].
     unfold table_numeric_next_y,table_numeric_next_x.
     setoid_rewrite HScale;setoid_rewrite IScale;ring.
   + transitivity ((k*z)*table_numeric_h (k*k*x) (k*z) qx);[exact ZRes|].
     setoid_rewrite HScale;ring.
Qed.
End TableMixedAlgebra.

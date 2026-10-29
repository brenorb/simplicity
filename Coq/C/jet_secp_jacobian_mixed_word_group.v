(** Interpret the original literal mixed-addition dispatch in the curve group.
    The context is shared-Z; its nonzero premise is internal and must be
    supplied by the caller's proved table invariant. All point branches are
    retained. This module does not yet give the extended returned ratio. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_field_word_group C.jet_secp_jacobian_group C.jet_secp_jacobian_word_group
 C.jet_secp_jacobian_mixed_group C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_nonzero_literal
 C.jet_secp_generator_point_numeric C.jet_secp_add_literal C.jet_secp_canonical_zero
 C.jet_secp_literal_gej_predicate C.jet_secp_literal_add_program C.jet_secp_curve_literal
 C.jet_secp_rescale_literal C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_canonical_normalize
 C.jet_secp_negate_literal_contract C.jet_secp_double_literal C.jet_secp_literal_infinity C.jet_toZ.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_jacobian_mixed_word_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Lemma secp_field_word_cube (x:Ty.tySem (Word 8)):
 secp_field_word (@literal_fe_cube Alg.CoreFunSem x)=
 GZnZ.mul feP (GZnZ.mul feP (secp_field_word x) (secp_field_word x)) (secp_field_word x).
Proof.
 unfold secp_field_word;rewrite literal_curve_cube_numeric,secp_field_integer_mod,
  !secp_field_integer_mul;reflexivity.
Qed.
Lemma secp_field_integer_minus_two:secp_field_integer (-2)=
 GZnZ.opp feP (GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP)).
Proof.
 change (secp_field_integer (-2)=GZnZ.opp feP (secp_field_integer 2)).
 exact (secp_field_integer_opp 2).
Qed.
Local Opaque secp_field_word secp_field_integer.
Lemma secp_mixed_literal_h_field (x z bx:Ty.tySem (Word 8)):
 secp_field_word (mixed_literal_h x z bx)=secp_jmixed_h (secp_field_word x) (secp_field_word z) (secp_field_word bx).
Proof.
 unfold mixed_literal_h;rewrite secp_field_word_add,!secp_field_word_mul,
  !secp_field_word_square,secp_field_word_negate,secp_field_word_one.
 unfold secp_jmixed_h,secp_group_field;ring.
Qed.
Lemma secp_mixed_literal_i_field (y z byword:Ty.tySem (Word 8)):
 secp_field_word (mixed_literal_i y z byword)=secp_jmixed_i (secp_field_word y) (secp_field_word z) (secp_field_word byword).
Proof.
 unfold mixed_literal_i;rewrite secp_field_word_add,!secp_field_word_mul,
  !secp_field_word_cube,secp_field_word_negate,secp_field_word_one.
 unfold secp_jmixed_i,secp_group_field;ring.
Qed.
Lemma secp_mixed_literal_nonzero_fields (h i u v z:Ty.tySem (Word 8)):
 secp_jacobian_word_fields ((mixed_literal_rx h i u,mixed_literal_ry h i u v),mixed_literal_rz h z)=
 ((secp_jmixed_x (secp_field_word h) (secp_field_word i) (secp_field_word u),
   secp_jmixed_y (secp_field_word h) (secp_field_word i) (secp_field_word u) (secp_field_word v)),
   GZnZ.mul feP (GZnZ.opp feP (secp_field_word h)) (secp_field_word z)).
Proof.
 unfold secp_jacobian_word_fields;cbn [fst snd].
 unfold mixed_literal_ry,mixed_literal_rz,mixed_literal_tx,mixed_literal_rx,mixed_literal_t.
 repeat first [rewrite secp_field_word_add|rewrite secp_field_word_mul|
  rewrite secp_field_word_square|rewrite secp_field_word_negate|rewrite secp_field_word_cube|
  rewrite secp_field_word_multiply_int|rewrite secp_field_integer_minus_two|rewrite secp_field_word_one].
 f_equal;[f_equal|];unfold secp_jmixed_y,secp_jmixed_x,secp_group_field;ring.
Qed.
Lemma secp_field_word_flag_true (x:Ty.tySem (Word 8)):
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem x)=Datatypes.true <->secp_field_word x=GZnZ.zero feP.
Proof. rewrite <-secp_field_word_zero_test;apply (SMain.is_zero_correct secp_group_theory). Qed.
Lemma secp_field_word_flag_false (x:Ty.tySem (Word 8)):
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem x)=Datatypes.false ->secp_field_word x<>GZnZ.zero feP.
Proof.
 intros Flag Zero;pose proof (proj2 (secp_field_word_flag_true x) Zero);congruence.
Qed.
Lemma secp_mixed_literal_u_field (x:Ty.tySem (Word 8)):
 secp_field_word (@literal_fe_multiply Alg.CoreFunSem
  (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)))=secp_field_word x.
Proof.
 rewrite secp_field_word_mul,secp_field_word_square,secp_field_word_one;unfold secp_group_field;ring.
Qed.
Lemma secp_mixed_literal_v_field (y:Ty.tySem (Word 8)):
 secp_field_word (@literal_fe_multiply Alg.CoreFunSem
  (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)))=secp_field_word y.
Proof.
 rewrite secp_field_word_mul,secp_field_word_cube,secp_field_word_one;unfold secp_group_field;ring.
Qed.
Lemma secp_literal_affine_word_rep (c:secp_group_field) (bx byword:Ty.tySem (Word 8)) (q:secp_group_point):
 secp_jacobian_word_rep c ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt) q ->
 exists B:secp_jacobian_curve (secp_field_word bx) (secp_field_word byword) c,
 secp_jacobian_group_value (secp_field_word bx) (secp_field_word byword) c B=q.
Proof.
 unfold secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep;cbn [fst snd].
 rewrite secp_field_word_one.
 replace (GZnZ.mul feP c (GZnZ.one feP)) with c by (unfold secp_group_field in *;ring).
 exact (fun R=>R).
Qed.
Lemma secp_literal_mixed_nonzero_group (c:secp_group_field) (x y z bx byword:Ty.tySem (Word 8)) (p q:secp_group_point):
 c<>GZnZ.zero feP ->secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt) q ->
 secp_field_word z<>GZnZ.zero feP ->secp_field_word (mixed_literal_h x z bx)<>GZnZ.zero feP ->
 let h:=mixed_literal_h x z bx in let i:=mixed_literal_i y z byword in
 let u:=@literal_fe_multiply Alg.CoreFunSem
  (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) in
 let v:=@literal_fe_multiply Alg.CoreFunSem
  (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) in
 secp_jacobian_word_rep c ((mixed_literal_rx h i u,mixed_literal_ry h i u v),mixed_literal_rz h z)
 (SMain.add secp_group_theory p q).
Proof.
 intros C RA RB Z Hbranch;cbn zeta.
 destruct RA as [A ValueA];destruct (secp_literal_affine_word_rep c bx byword q RB) as [B ValueB].
 rewrite secp_mixed_literal_h_field in Hbranch.
 unfold secp_jacobian_word_rep;rewrite secp_mixed_literal_nonzero_fields,
  secp_mixed_literal_h_field,secp_mixed_literal_i_field,secp_mixed_literal_u_field,secp_mixed_literal_v_field.
 unfold secp_jacobian_context_rep.
 exists (secp_jacobian_mixed_curve _ _ _ _ _ _ A B).
 exact (eq_trans (secp_jacobian_mixed_finite_group _ _ _ _ _ _ A B C Z Hbranch)
  (f_equal2 (SMain.add secp_group_theory) ValueA ValueB)).
Qed.
Lemma secp_literal_mixed_group (c:secp_group_field) (x y z bx byword:Ty.tySem (Word 8)) (p q:secp_group_point):
 c<>GZnZ.zero feP ->secp_jacobian_word_rep c ((x,y),z) p ->
 secp_jacobian_word_rep c ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt) q ->
 secp_jacobian_word_rep c (@literal_gej_ge_add Alg.CoreFunSem (((x,y),z),(bx,byword)))
 (SMain.add secp_group_theory p q).
Proof.
 intros C RA RB;pose proof RA as RepA;destruct RA as [A ValueA].
 destruct (secp_literal_affine_word_rep c bx byword q RB) as [B ValueB].
 rewrite literal_mixed_step;cbn zeta.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)) eqn:Zflag.
 - pose proof (proj1 (secp_field_word_flag_true z) Zflag) as Zzero.
   assert (Infinity:p=secp_group_infinity).
   { transitivity (secp_jacobian_group_value (secp_field_word x) (secp_field_word y)
      (GZnZ.mul feP c (secp_field_word z)) A).
     - symmetry;exact ValueA.
     - apply secp_jacobian_group_infinity_iff;rewrite Zzero;unfold secp_group_field;ring. }
   rewrite Infinity,SMain.add_0_l.
   unfold secp_jacobian_word_rep.
   change (secp_jacobian_context_rep c
    ((secp_field_word (@canonical_fe_normalize Alg.CoreFunSem bx),
      secp_field_word (@canonical_fe_normalize Alg.CoreFunSem byword)),
      secp_field_word (@canonical_fe_normalize Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))) q).
   rewrite !secp_field_word_normalize,secp_field_word_one.
   unfold secp_jacobian_context_rep.
   replace (GZnZ.mul feP c (GZnZ.one feP)) with c by (unfold secp_group_field in *;ring).
   exists B;exact ValueB.
 - pose proof (secp_field_word_flag_false z Zflag) as Z.
   destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx))) eqn:Hflag.
   + pose proof (proj1 (secp_field_word_flag_true (mixed_literal_h x z bx)) Hflag) as Hbranch.
     rewrite secp_mixed_literal_h_field in Hbranch.
     destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i y z byword))) eqn:Iflag.
     * pose proof (proj1 (secp_field_word_flag_true (mixed_literal_i y z byword)) Iflag) as Ibranch.
       rewrite secp_mixed_literal_i_field in Ibranch.
       pose proof (secp_jacobian_mixed_equal_group _ _ _ _ _ _ A B Z Hbranch Ibranch) as Same.
       assert (PointSame:p=q) by exact (eq_trans (eq_sym ValueA) (eq_trans Same ValueB)).
       replace q with p by exact PointSame;apply secp_literal_double_group;exact RepA.
     * pose proof (secp_field_word_flag_false (mixed_literal_i y z byword) Iflag) as Ibranch.
       rewrite secp_mixed_literal_i_field in Ibranch.
       pose proof (secp_jacobian_mixed_inverse_group _ _ _ _ _ _ A B Z Hbranch Ibranch) as Inverse.
       assert (PointInverse:p=SMain.opp secp_group_theory q).
       { exact (eq_trans (eq_sym ValueA) (eq_trans Inverse (f_equal (SMain.opp secp_group_theory) ValueB))). }
       assert (Sum:SMain.add secp_group_theory p q=secp_group_infinity).
       { rewrite PointInverse,SMain.add_comm;apply (SMain.add_opp secp_group_theory). }
       rewrite Sum;apply secp_literal_infinity_group.
   + apply secp_literal_mixed_nonzero_group;try assumption.
     apply secp_field_word_flag_false;exact Hflag.
Qed.

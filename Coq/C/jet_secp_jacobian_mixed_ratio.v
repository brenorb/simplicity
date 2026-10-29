(** The original extended mixed-addition routing and its finite-input field
    ratio identity. This preserves the literal returned word, including the
    double branch's unreduced Y word. The projection identity is not a raw jet
    equivalence and does not alter the existing divergence classification. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_add_literal C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_nonzero_literal
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize C.jet_secp_negate_literal_contract
 C.jet_secp_square_execution C.jet_secp_rescale_literal C.jet_secp_double_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_infinity C.jet_secp_literal_gej_predicate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
 literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity.
Lemma literal_mixed_extended_finite_step (x y z bx byword:Ty.tySem (Word 8)):
 @literal_gej_is_infinity Alg.CoreFunSem ((x,y),z)=inl tt ->
 let h:=mixed_literal_h x z bx in let i:=mixed_literal_i y z byword in
 let u:=@literal_fe_multiply Alg.CoreFunSem
  (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) in
 let v:=@literal_fe_multiply Alg.CoreFunSem
  (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)) in
 @literal_gej_ge_add_ex Alg.CoreFunSem (((x,y),z),(bx,byword))=
 if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem h) then
  if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem i) then
   (y,@literal_gej_double Alg.CoreFunSem ((x,y),z))
  else (@literal_fe_zero256 Alg.CoreFunSem tt,@literal_gej_infinity Alg.CoreFunSem tt)
 else (@literal_fe_multiply Alg.CoreFunSem
   (h,@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)),
   ((mixed_literal_rx h i u,mixed_literal_ry h i u v),mixed_literal_rz h z)).
Proof.
 intro Finite;cbn zeta.
 assert (Other:@literal_gej_is_infinity Alg.CoreFunSem
  ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
  by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 unfold literal_gej_ge_add_ex,literal_gej_add_ex.
 cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
 literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity].
 match goal with |- (match ?c with inl _=>_|inr _=>_ end)=_ =>
  assert (FC:c=inl tt) by exact Finite;rewrite FC end.
 match goal with |- (match ?c with inl _=>_|inr _=>_ end)=_ =>
  assert (SC:c=inl tt) by exact Other;rewrite SC end.
 let left:=constr:(match @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx) with
 | inl _=>
  (@literal_fe_multiply Alg.CoreFunSem
    (mixed_literal_h x z bx,@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)),
   ((mixed_literal_rx (mixed_literal_h x z bx) (mixed_literal_i y z byword)
      (@literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))),
     mixed_literal_ry (mixed_literal_h x z bx) (mixed_literal_i y z byword)
      (@literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)))
      (@literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)))),
     mixed_literal_rz (mixed_literal_h x z bx) z))
 | inr _=>match @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i y z byword) with
   | inl _=>(@literal_fe_zero256 Alg.CoreFunSem tt,@literal_gej_infinity Alg.CoreFunSem tt)
   | inr _=>(y,@literal_gej_double Alg.CoreFunSem ((x,y),z)) end
 end) in
 match goal with |- _ = ?right => change (left=right) end.
 destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx)) as [a|a];destruct a.
 - reflexivity.
 - destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i y z byword)) as [b|b];destruct b;reflexivity.
Qed.
From Coq Require Import Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_field_word_group C.jet_secp_jacobian_word_group.
Add Field secp_mixed_ratio_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque secp_field_word.
Lemma literal_double_finite_z_field (x y z:Ty.tySem (Word 8)):
 @literal_gej_is_infinity Alg.CoreFunSem ((x,y),z)=inl tt ->
 secp_field_word (snd (@literal_gej_double Alg.CoreFunSem ((x,y),z)))=
 GZnZ.mul feP (secp_field_word y) (secp_field_word z).
Proof.
 intro Finite;rewrite literal_gej_double_step,Finite;cbn [Bit.toBool].
 exact (f_equal (@snd (secp_group_field*secp_group_field) secp_group_field)
  (secp_literal_double_body_fields x y z)).
Qed.
Lemma literal_infinity_z_field:
 secp_field_word (snd (@literal_gej_infinity Alg.CoreFunSem tt))=GZnZ.zero feP.
Proof.
 exact (f_equal (@snd (secp_group_field*secp_group_field) secp_group_field) secp_literal_infinity_fields).
Qed.
Local Transparent literal_fe_zero256.
Lemma literal_zero_field:
 secp_field_word (@literal_fe_zero256 Alg.CoreFunSem tt)=GZnZ.zero feP.
Proof. exact secp_field_word_zero. Qed.
Theorem literal_mixed_finite_ratio_field (x y z bx byword:Ty.tySem (Word 8)):
 @literal_gej_is_infinity Alg.CoreFunSem ((x,y),z)=inl tt ->
 let result:=@literal_gej_ge_add_ex Alg.CoreFunSem (((x,y),z),(bx,byword)) in
 secp_field_word (snd (snd result))=
 GZnZ.mul feP (secp_field_word (fst result)) (secp_field_word z).
Proof.
 intro Finite;cbn zeta;rewrite literal_mixed_extended_finite_step by exact Finite.
 cbn zeta.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h x z bx))).
 - destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i y z byword)));
   cbn [fst snd].
   + apply literal_double_finite_z_field;exact Finite.
   + transitivity (GZnZ.zero feP);[exact literal_infinity_z_field|].
     symmetry;rewrite literal_zero_field;unfold secp_group_field;ring.
 - cbn [fst snd];unfold mixed_literal_rz;rewrite !secp_field_word_mul;
   unfold secp_group_field;ring.
Qed.

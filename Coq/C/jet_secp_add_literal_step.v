(** Finite dispatch of the fixed literal addition tree. This exposes the
    exact coordinates needed by the original C mixed-addition bridge. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_add_literal C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
 C.jet_secp_negate_literal_contract C.jet_secp_square_execution C.jet_secp_multiply_literal_spec
 C.jet_secp_literal_add_program C.jet_secp_rescale_literal C.jet_secp_double_literal
 C.jet_secp_literal_infinity C.jet_secp_literal_gej_predicate C.jet_secp_curve_literal.
Set Default Timeout 10.
Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
 literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity.
Lemma literal_gej_add_finite_step (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt ->
 @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),bz)=inl tt ->
 let h := @literal_fe_add Alg.CoreFunSem
   (@literal_fe_multiply Alg.CoreFunSem (ax,@literal_fe_square Alg.CoreFunSem bz),
    @literal_fe_multiply Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem bx,@literal_fe_square Alg.CoreFunSem az)) in
 let i := @literal_fe_add Alg.CoreFunSem
   (@literal_fe_multiply Alg.CoreFunSem (ay,@literal_fe_cube Alg.CoreFunSem bz),
    @literal_fe_multiply Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem byword,@literal_fe_cube Alg.CoreFunSem az)) in
 let t := @literal_fe_multiply Alg.CoreFunSem
   (@literal_fe_square Alg.CoreFunSem h,@literal_fe_multiply Alg.CoreFunSem (ax,@literal_fe_square Alg.CoreFunSem bz)) in
 let g := @literal_fe_cube Alg.CoreFunSem h in
 let rx := @literal_fe_add Alg.CoreFunSem
   (@literal_fe_add Alg.CoreFunSem (g,@literal_fe_multiply_int (-2) Alg.CoreFunSem t),@literal_fe_square Alg.CoreFunSem i) in
 snd (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))=
 match @canonical_fe_is_zero Alg.CoreFunSem h with
 | inl _ => ((rx,@literal_fe_add Alg.CoreFunSem
     (@literal_fe_multiply Alg.CoreFunSem (g,@literal_fe_multiply Alg.CoreFunSem (ay,@literal_fe_cube Alg.CoreFunSem bz)),
      @literal_fe_multiply Alg.CoreFunSem (i,@literal_fe_add Alg.CoreFunSem (rx,@literal_fe_negate Alg.CoreFunSem t)))),
     @literal_fe_multiply Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (h,az),@literal_fe_negate Alg.CoreFunSem bz))
 | inr _ => match @canonical_fe_is_zero Alg.CoreFunSem i with
   | inl _ => @literal_gej_infinity Alg.CoreFunSem tt
   | inr _ => @literal_gej_double Alg.CoreFunSem ((ax,ay),az)
   end
 end.
Proof.
 intros HA HB;cbn zeta.
 unfold literal_gej_add_ex.
 cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
 literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity].
 match goal with |- snd (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC : c=inl tt) by exact HA;rewrite HC end.
 match goal with |- snd (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC' : c=inl tt) by exact HB;rewrite HC' end.
 match goal with |- snd (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   destruct c as [u|u];destruct u end.
 - reflexivity.
 - match goal with |- snd (match ?c with inl _ => _ | inr _ => _ end)=_ =>
     destruct c as [u|u];destruct u end;reflexivity.
Qed.

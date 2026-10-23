(** Closed flag bridges for incoming infinity and the finite H=0 branches.
    The nonzero-H branch still needs a separately proved nonzero-product fact;
    no public equivalence registration is justified by this module alone. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_field_negate_separate C.jet_secp_field_weak_loose C.jet_secp_field_weak_tight
 C.jet_secp_multiply_input_input C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal
 C.jet_secp_double_coordinate_numeric C.jet_secp_mixed_dispatch_literal
 C.jet_secp_mixed_finite_return C.jet_secp_mixed_zero_return C.jet_secp_mixed_body_loose
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_curve_literal
 C.jet_secp_gej_ge_equiv_dispatch C.jet_secp_gej_ge_equiv_reader C.jet_secp_gej_ge_equiv_function
 C.jet_secp_gej_ge_equiv_literal C.jet_secp_gej_negate_literal C.jet_secp_gej_negate_parametric
 C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity C.jet_secp_add_literal
 C.jet_secp_add_literal_step C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program
 C.jet_secp_double_literal C.jet_secp_double_var_owned C.jet_secp_square_execution
 C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_reader_rho negate_sep_words weak_loose_words
 canonical_fe_normalize canonical_fe_is_zero literal_fe_negate normalized_value
 literal_gej_ge_equiv literal_gej_ge_add literal_gej_is_infinity literal_gej_infinity
 literal_gej_double literal_gej_double_body literal_fe_one256.
Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_multiply_int literal_fe_halve.

Lemma equiv_normalized_zero_test (a : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem a))=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem a).
Proof.
 rewrite !literal_curve_zero_numeric,canonical_fe_normalize_numeric,
  canonical_field_order_matches_limb_model,Z.mod_mod by (unfold feP,feR;lia).
 reflexivity.
Qed.

Lemma equiv_finite_nonzero_h_reduction (x y z u v : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)=false ->
 Z.eqb (radix_value (mixed_h_words (square_reader_rho x) (square_reader_rho z)
  (square_reader_rho u)) mod feP) 0=false ->
 gej_ge_equiv_reader_bit x y z u v=false /\
 Bit.toBool (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v)))=
 Z.eqb ((@toZ (WordToZ 8) (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
   (@canonical_fe_normalize Alg.CoreFunSem z) u)*
   @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem z)*(feP-1)) mod feP) 0.
Proof.
 intros Fin HNonzero;split.
 - unfold gej_ge_equiv_reader_bit,gej_ge_equiv_bit,gej_ge_equiv_result,mixed_loose_body_flag.
   rewrite Fin.
   change (Int.eq (mixed_loose_finite_flag (square_reader_rho x)
    (negate_sep_words (square_reader_rho y)) (square_reader_rho z)
    (square_reader_rho u) (square_reader_rho v)) Int.one=false).
   unfold mixed_loose_finite_flag;rewrite HNonzero;reflexivity.
 - assert (NA : @literal_gej_is_infinity Alg.CoreFunSem
    ((@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y),
      @canonical_fe_normalize Alg.CoreFunSem z)=inl tt).
   { rewrite literal_gej_is_infinity_value.
     pose proof (equiv_normalized_zero_test z) as NZ;rewrite Fin in NZ.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem z)) as [b|b];
      destruct b;[reflexivity|discriminate NZ]. }
   assert (NB : @literal_gej_is_infinity Alg.CoreFunSem ((u,v),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
    by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
   assert (NH : @canonical_fe_is_zero Alg.CoreFunSem
    (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
      (@canonical_fe_normalize Alg.CoreFunSem z) u)=inl tt).
   { rewrite equiv_negated_h_test in HNonzero.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem
      (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
       (@canonical_fe_normalize Alg.CoreFunSem z) u)) as [b|b];destruct b;
      [reflexivity|discriminate HNonzero]. }
   rewrite literal_gej_ge_equiv_step,literal_gej_negate_step,literal_gej_ge_add_expansion.
   pose proof (literal_gej_add_finite_step _ _ _ _ _ _ NA NB) as Add.
   cbv zeta in Add.
   fold (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
    (@canonical_fe_normalize Alg.CoreFunSem z) u) in Add.
   rewrite NH in Add.
   pose proof (f_equal (fun p : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) =>
    Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem p)) Add) as FlagAdd.
   etransitivity;[exact FlagAdd|].
   rewrite literal_gej_is_infinity_value,literal_curve_zero_numeric,!literal_multiply_numeric,
    literal_curve_negate_numeric,literal_fe_one256_value.
   repeat rewrite Z.mul_mod_idemp_l by (unfold feP,feR;lia).
   repeat rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
   rewrite Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma equiv_double_body_flag x y z (a b c : Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) b mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
 Int.eq (double_var_zflag y z) Int.one=
 Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
  (@literal_gej_double_body Alg.CoreFunSem ((a,b),c))).
Proof.
 intros BX BY BZ HX HY HZ.
 pose proof (proj2 (proj2 (double_body_coordinates_match x y z a b c BX BY BZ HX HY HZ))) as RZ.
 destruct (@literal_gej_double_body Alg.CoreFunSem ((a,b),c)) as [[rx ry] rz].
 cbn [snd] in RZ.
 rewrite literal_gej_is_infinity_value,literal_curve_zero_numeric.
 assert (RR : @toZ (WordToZ 8) rz mod feP=@toZ (WordToZ 8) rz).
 { rewrite <-RZ,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 unfold double_var_zflag;rewrite RZ,RR.
 destruct (Z.eqb (@toZ (WordToZ 8) rz) 0);reflexivity.
Qed.

Lemma equiv_literal_infinity_flag :
 Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt))=true.
Proof.
 change (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt))=true).
 rewrite literal_curve_zero_numeric.
 unfold literal_fe_zero256;rewrite Word.zero_correct;reflexivity.
Qed.

Lemma equiv_incoming_infinity (x y z u v : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)=true ->
 gej_ge_equiv_reader_bit x y z u v=
 Bit.toBool (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v))).
Proof.
 intro Inf.
 assert (NI : @literal_gej_is_infinity Alg.CoreFunSem
  ((@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y),
    @canonical_fe_normalize Alg.CoreFunSem z)=inr tt).
 { rewrite literal_gej_is_infinity_value.
   pose proof (equiv_normalized_zero_test z) as NZ;rewrite Inf in NZ.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem z)) as [b|b];
    destruct b;[discriminate NZ|reflexivity]. }
 rewrite literal_gej_ge_equiv_step,literal_gej_negate_step,literal_gej_ge_add_infinite by exact NI.
 rewrite literal_gej_is_infinity_value,equiv_normalized_zero_test,mixed_literal_one_finite.
 unfold gej_ge_equiv_reader_bit,gej_ge_equiv_bit,gej_ge_equiv_result,mixed_loose_body_flag.
 rewrite Inf;reflexivity.
Qed.

Lemma equiv_finite_zero_h (x y z u v : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)=false ->
 Z.eqb (radix_value (mixed_h_words (square_reader_rho x) (square_reader_rho z)
  (square_reader_rho u)) mod feP) 0=true ->
 gej_ge_equiv_reader_bit x y z u v=
 Bit.toBool (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v))).
Proof.
 intros Fin HZero.
 assert (NA : @literal_gej_is_infinity Alg.CoreFunSem
  ((@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y),
    @canonical_fe_normalize Alg.CoreFunSem z)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   pose proof (equiv_normalized_zero_test z) as NZ;rewrite Fin in NZ.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem z)) as [b|b];
    destruct b;[reflexivity|discriminate NZ]. }
 assert (NB : @literal_gej_is_infinity Alg.CoreFunSem ((u,v),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
  by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 assert (NH : @canonical_fe_is_zero Alg.CoreFunSem
  (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
    (@canonical_fe_normalize Alg.CoreFunSem z) u)=inr tt).
 { rewrite equiv_negated_h_test in HZero.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem
    (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
     (@canonical_fe_normalize Alg.CoreFunSem z) u)) as [b|b];destruct b;
    [discriminate HZero|reflexivity]. }
 rewrite literal_gej_ge_equiv_step,literal_gej_negate_step,literal_gej_ge_add_expansion.
 pose proof (literal_gej_add_finite_step _ _ _ _ _ _ NA NB) as Add.
 cbv zeta in Add.
 fold (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
  (@canonical_fe_normalize Alg.CoreFunSem z) u)
  (mixed_literal_i (@literal_fe_negate Alg.CoreFunSem y) (@canonical_fe_normalize Alg.CoreFunSem z) v) in Add.
 rewrite NH in Add.
 lazymatch type of Add with @eq ?A ?lhs ?rhs =>
   pose proof (@f_equal A bool
     (fun p : A => Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem p))
     lhs rhs Add) as FlagAdd
 end.
 etransitivity;[|exact (eq_sym FlagAdd)].
 unfold gej_ge_equiv_reader_bit,gej_ge_equiv_bit,gej_ge_equiv_result,mixed_loose_body_flag.
 rewrite Fin.
 change (Int.eq (mixed_loose_finite_flag (square_reader_rho x)
  (negate_sep_words (square_reader_rho y)) (square_reader_rho z)
  (square_reader_rho u) (square_reader_rho v)) Int.one=
  Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
   (match @canonical_fe_is_zero Alg.CoreFunSem
    (mixed_literal_i (@literal_fe_negate Alg.CoreFunSem y) (@canonical_fe_normalize Alg.CoreFunSem z) v) with
   | inl _ => @literal_gej_infinity Alg.CoreFunSem tt
   | inr _ => @literal_gej_double Alg.CoreFunSem
    ((@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y),
     @canonical_fe_normalize Alg.CoreFunSem z)
   end))).
 unfold mixed_loose_finite_flag;rewrite HZero.
 unfold mixed_zero_flag;rewrite equiv_negated_i_test.
 destruct (@canonical_fe_is_zero Alg.CoreFunSem
  (mixed_literal_i (@literal_fe_negate Alg.CoreFunSem y) (@canonical_fe_normalize Alg.CoreFunSem z) v))
  as [b|b];destruct b;cbn [Bit.toBool].
 - rewrite equiv_literal_infinity_flag;reflexivity.
 - rewrite literal_gej_double_step,NA.
   change (Int.eq (double_var_zflag (negate_sep_words (square_reader_rho y)) (square_reader_rho z)) Int.one=
    Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
     (@literal_gej_double_body Alg.CoreFunSem
       ((@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y),
         @canonical_fe_normalize Alg.CoreFunSem z)))).
   apply equiv_double_body_flag with (x:=square_reader_rho x).
   + apply square_reader_bounds.
   + apply gej_ge_equiv_negated_bounds;apply normalized_value_range.
   + apply square_reader_bounds.
   + apply equiv_normalized_reader_residue.
   + apply double_match_mod;apply equiv_negated_reader_residue.
   + apply equiv_normalized_reader_residue.
Qed.

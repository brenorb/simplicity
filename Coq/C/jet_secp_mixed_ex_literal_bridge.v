(** Original mixed-addition helper outputs, ratio included, against the
    unchanged fixed literal extended program.  The point output always equals
    the literal point.  The ratio equals the literal ratio after field
    normalization; the only literal ratio that is not already canonical is the
    reported equal-point input Y (see JET_SECP_RATIO_MISMATCHES.md). *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge C.jet_secp_field_weak_tight
 C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_difference C.jet_secp_mixed_finite_prefix C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_finite_body C.jet_secp_mixed_nonzero_tail C.jet_secp_mixed_nonzero_literal
 C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_infinite_literal C.jet_secp_mixed_body
 C.jet_secp_mixed_literal_bridge C.jet_secp_mixed_finite_ratio C.jet_secp_mixed_function_ratio
 C.jet_secp_mixed_ratio_branches C.jet_secp_mixed_zero_return C.jet_secp_add_literal C.jet_secp_add_literal_step
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize
 C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity C.jet_secp_rescale_literal
 C.jet_secp_square_execution C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program
 C.jet_secp_literal_add_numeric C.jet_secp_double_literal_bridge C.jet_secp_negate_literal_contract
 C.jet_secp_curve_literal C.jet_secp_double_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words rescale_field_output
 literal_gej_ge_add literal_gej_ge_add_ex literal_gej_add_ex literal_gej_is_infinity canonical_fe_is_zero
 canonical_fe_normalize literal_fe_multiply literal_fe_square literal_fe_cube literal_fe_one256
 literal_fe_zero256 literal_fe_add literal_fe_negate literal_fe_multiply_int literal_gej_double
 literal_gej_infinity.

Lemma word8_toZ_nonneg (x : Ty.tySem (Word 8)) : 0 <= @toZ (WordToZ 8) x.
Proof.
 pose proof (@toZ_mod (WordToZ 8) x) as HT.
 assert (HM : 0 < two_power_nat (bitSize (WordToZ 8))).
 { rewrite two_power_nat_equiv;apply Z.pow_pos_nonneg;lia. }
 pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) x) _ HM) as HB.
 rewrite <-HT in HB;exact (proj1 HB).
Qed.

Lemma canonical_fe_normalize_reduced (x : Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) x < feP -> @canonical_fe_normalize Alg.CoreFunSem x=x.
Proof.
 intro HL;apply (toZ_injective (WordToZ 8)).
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
 apply Z.mod_small;split;[|exact HL].
 pose proof (word8_toZ_nonneg x) as HR;lia.
Qed.

Lemma canonical_fe_normalize_zero256 :
 @canonical_fe_normalize Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt)=@literal_fe_zero256 Alg.CoreFunSem tt.
Proof.
 apply canonical_fe_normalize_reduced.
 change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt) < feP).
 rewrite Word.zero_correct;unfold feP,feR;lia.
Qed.

Lemma literal_gej_add_ex_fst_infinite (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt ->
 fst (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))=@literal_fe_zero256 Alg.CoreFunSem tt.
Proof. intro HInf;rewrite literal_gej_add_ex_infinite by exact HInf;reflexivity. Qed.

Local Transparent literal_gej_add_ex.
Ltac literal_ex_open HAin :=
 unfold literal_gej_add_ex;
 cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
 literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity];
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC : c=inl tt) by exact HAin;rewrite HC end;
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC' : c=inl tt) by exact mixed_literal_one_finite;rewrite HC' end.

Lemma literal_gej_add_ex_fst_nonzero_h (ax ay az bx byword : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inl tt ->
 fst (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)))=
 @literal_fe_multiply Alg.CoreFunSem (mixed_literal_h ax az bx,
   @literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)).
Proof.
 intros HA HZH;unfold mixed_literal_h in HZH.
 literal_ex_open HA.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC'' : c=inl tt) by exact HZH;rewrite HC'' end.
 reflexivity.
Qed.

Lemma literal_gej_add_ex_fst_zero_h_nonzero_i (ax ay az bx byword : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)=inl tt ->
 fst (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)))=
 @literal_fe_zero256 Alg.CoreFunSem tt.
Proof.
 intros HA HZH HZI;unfold mixed_literal_h in HZH;unfold mixed_literal_i in HZI.
 literal_ex_open HA.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC'' : c=inr tt) by exact HZH;rewrite HC'' end.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC3 : c=inl tt) by exact HZI;rewrite HC3 end.
 reflexivity.
Qed.

Lemma literal_gej_add_ex_fst_equal_point (ax ay az bx byword : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)=inr tt ->
 fst (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)))=ay.
Proof.
 intros HA HZH HZI;unfold mixed_literal_h in HZH;unfold mixed_literal_i in HZI.
 literal_ex_open HA.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC'' : c=inr tt) by exact HZH;rewrite HC'' end.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC3 : c=inr tt) by exact HZI;rewrite HC3 end.
 reflexivity.
Qed.
Local Opaque literal_gej_add_ex.

(** The literal ratio of the extended program is the first projection. *)
Lemma literal_gej_ge_add_ex_expansion (a : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
    (b : Ty.tySem (Ty.Prod (Word 8) (Word 8))) :
 @literal_gej_ge_add_ex Alg.CoreFunSem (a,b)=
 @literal_gej_add_ex Alg.CoreFunSem (a,(b,@literal_fe_one256 Alg.CoreFunSem tt)).
Proof. reflexivity. Qed.

Theorem mixed_ex_ratio_reader_literal (ax ay az bx byword : Ty.tySem (Word 8)) :
 let flag := bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 rescale_field_output (mixed_body_ratio_words flag (square_reader_rho ax) (square_reader_rho ay)
   (square_reader_rho az) (square_reader_rho bx) (square_reader_rho byword))=
 @canonical_fe_normalize Alg.CoreFunSem
   (fst (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))).
Proof.
 cbv zeta;unfold mixed_body_ratio_words,bit_int;rewrite literal_gej_ge_add_ex_expansion.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:HInf.
 - change (rescale_field_output (fun _ : nat=>Int64.zero)=
     @canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_add_ex Alg.CoreFunSem
       (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt))))).
   assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt).
   { rewrite literal_gej_is_infinity_value.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [u|u];destruct u;[discriminate HInf|reflexivity]. }
   rewrite literal_gej_add_ex_fst_infinite by exact HA.
   rewrite canonical_fe_normalize_zero256;exact zero_field_writer_literal_output.
 - change (rescale_field_output (mixed_finite_ratio_words (square_reader_rho ax) (square_reader_rho ay)
     (square_reader_rho az) (square_reader_rho bx) (square_reader_rho byword))=
     @canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_add_ex Alg.CoreFunSem
       (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt))))).
   assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
   { rewrite literal_gej_is_infinity_value.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [u|u];destruct u;[reflexivity|discriminate HInf]. }
   assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
     by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
   unfold mixed_finite_ratio_words.
   destruct (Z.eqb (radix_value (mixed_h_words (square_reader_rho ax) (square_reader_rho az)
     (square_reader_rho bx)) mod feP) 0) eqn:HH.
   + (* H = 0 *)
     assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt).
     { rewrite mixed_h_reader_test in HH.
       destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [u|u];destruct u;
         [discriminate HH|reflexivity]. }
     unfold mixed_zero_words;rewrite mixed_i_reader_test.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)) as [u|u] eqn:HI;destruct u;cbn [Bit.toBool].
     * rewrite literal_gej_add_ex_fst_zero_h_nonzero_i by assumption.
       change (rescale_field_output (fun _ : nat=>Int64.zero)=
         @canonical_fe_normalize Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt)).
       rewrite canonical_fe_normalize_zero256;exact zero_field_writer_literal_output.
     * rewrite literal_gej_add_ex_fst_equal_point by assumption.
       exact (mixed_reader_output ay).
   + (* H <> 0 *)
     assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inl tt).
     { rewrite mixed_h_reader_test in HH.
       destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [u|u];destruct u;
         [reflexivity|discriminate HH]. }
     rewrite literal_gej_add_ex_fst_nonzero_h by assumption.
     set (h := mixed_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx)).
     set (a := mixed_literal_h ax az bx).
     assert (RH : radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP).
     { unfold h,a;rewrite mixed_literal_h_numeric.
       change (radix_value (mixed_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx)) mod feP=
        (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP) mod feP).
       rewrite Zminus_mod_idemp_r.
       replace (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az)) with
        (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az-@toZ (WordToZ 8) ax) by ring.
       apply mixed_h_residue;try apply square_reader_bounds;
         try (apply mixed_positioned_tight;apply square_reader_positioned);
         rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
     assert (Value : rescale_field_output h=@literal_fe_multiply Alg.CoreFunSem
       (a,@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
     { apply (toZ_injective (WordToZ 8)).
       rewrite rescale_field_output_value,literal_multiply_numeric,literal_curve_negate_numeric,
         literal_fe_one256_value,field_prime_matches_normalizer,RH.
       rewrite Z.mul_mod_idemp_r by (unfold feP,feR;lia).
       replace (@toZ (WordToZ 8) a*((feP-1) mod feP)) with (@toZ (WordToZ 8) a*(feP-1)) at 1.
       2:{ rewrite Z.mod_small by (unfold feP,feR;lia);reflexivity. }
       replace (@toZ (WordToZ 8) a*(feP-1)) with (-@toZ (WordToZ 8) a+@toZ (WordToZ 8) a*feP) by ring.
       rewrite Z.mod_add by (unfold feP,feR;lia);reflexivity. }
     rewrite Value;symmetry;apply canonical_fe_normalize_reduced.
     rewrite literal_multiply_numeric.
     pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) a*@toZ (WordToZ 8)
       (@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))) feP
       ltac:(unfold feP,feR;lia)) as HB';lia.
Qed.

Theorem mixed_ex_reader_outputs_literal (ax ay az bx byword : Ty.tySem (Word 8)) :
 let flag := bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 (rescale_field_output (mixed_body_ratio_words flag (square_reader_rho ax) (square_reader_rho ay)
    (square_reader_rho az) (square_reader_rho bx) (square_reader_rho byword)),
  ((rescale_field_output (mixed_body_x_words flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)),
   rescale_field_output (mixed_body_y_words flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword))),
   rescale_field_output (mixed_body_z_words flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword))))=
 (@canonical_fe_normalize Alg.CoreFunSem
    (fst (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))),
  snd (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))).
Proof.
 intro flag;f_equal.
 - exact (mixed_ex_ratio_reader_literal ax ay az bx byword).
 - exact (mixed_reader_outputs_literal ax ay az bx byword).
Qed.

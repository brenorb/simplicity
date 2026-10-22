(** All branches of the original mixed-addition helper, on actual reader
    outputs, against the complete fixed literal Simplicity program. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge C.jet_secp_field_weak_tight
 C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_double_coordinate_numeric
 C.jet_secp_mixed_difference C.jet_secp_mixed_finite_prefix C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_finite_body C.jet_secp_mixed_nonzero_tail C.jet_secp_mixed_nonzero_literal
 C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_infinite_literal C.jet_secp_mixed_body C.jet_secp_mixed_function
 C.jet_secp_add_literal C.jet_secp_add_literal_step C.jet_secp_canonical_zero C.jet_secp_canonical_normalize
 C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity C.jet_secp_rescale_literal
 C.jet_secp_square_execution C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program
 C.jet_secp_literal_add_numeric C.jet_secp_double_literal_bridge C.jet_secp_negate_literal_contract
 C.jet_secp_curve_literal C.jet_secp_double_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words rescale_field_output
 literal_gej_ge_add literal_gej_is_infinity canonical_fe_is_zero literal_fe_multiply
 literal_fe_square literal_fe_cube literal_fe_one256 literal_fe_zero256
 literal_fe_add literal_fe_negate literal_fe_multiply_int literal_gej_double literal_gej_infinity.

Theorem mixed_nonzero_reader_outputs_literal (ax ay az bx byword : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 Z.eqb (radix_value (mixed_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx)) mod feP) 0=Datatypes.false ->
 ((rescale_field_output (mixed_finite_x_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)),
   rescale_field_output (mixed_finite_y_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword))),
   rescale_field_output (mixed_finite_z_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros HFin HH.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [u|u];destruct u;[reflexivity|discriminate HFin]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
   by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inl tt).
 { rewrite mixed_h_reader_test in HH.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [u|u];destruct u;
     [reflexivity|discriminate HH]. }
 unfold mixed_finite_x_words,mixed_finite_y_words,mixed_finite_z_words;rewrite HH.
 rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta;fold (mixed_literal_h ax az bx) (mixed_literal_i ay az byword);rewrite HZH.
 set (h := mixed_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx)).
 set (i := mixed_i_words (square_reader_rho ay) (square_reader_rho az) (square_reader_rho byword)).
 set (a := mixed_literal_h ax az bx);set (b := mixed_literal_i ay az byword).
 set (c := @literal_fe_multiply Alg.CoreFunSem (ax,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 set (d := @literal_fe_multiply Alg.CoreFunSem (ay,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 change (((rescale_field_output (mixed_nonzero_x_words h i (square_reader_rho ax)),
   rescale_field_output (mixed_nonzero_y_words h i (square_reader_rho ax) (square_reader_rho ay))),
   rescale_field_output (point_mul_words (square_reader_rho az) h))=
   ((mixed_literal_rx a b c,mixed_literal_ry a b c d),mixed_literal_rz a az)).
 assert (BH : square_input_bounds h).
 { unfold h,mixed_h_words;apply (proj2 (mixed_difference_numeric _ _
    (mixed_positioned_tight _ (square_reader_positioned ax))
    (double_mul_tight _ _ (square_reader_bounds bx)
      (double_tight_loose _ (double_square_tight _ (square_reader_bounds az)))))). }
 assert (BI : square_input_bounds i).
 { unfold i,mixed_i_words;refine (proj2 (mixed_difference_numeric _ _ _ _)).
   - apply double_mul_tight;[|apply square_reader_bounds].
     apply double_tight_loose;apply double_mul_tight;[apply square_reader_bounds|].
     apply double_tight_loose;apply double_square_tight;apply square_reader_bounds.
   - apply mixed_positioned_tight;apply square_reader_positioned. }
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
 assert (RI : radix_value i mod feP=@toZ (WordToZ 8) b mod feP).
 { unfold i,b;rewrite mixed_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
   apply mixed_i_residue;try apply square_reader_bounds;
     try (apply mixed_positioned_tight;apply square_reader_positioned);
     rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 assert (RC : radix_value (square_reader_rho ax) mod feP=@toZ (WordToZ 8) c mod feP).
 { unfold c;rewrite literal_multiply_numeric,literal_square_numeric,literal_fe_one256_value.
   rewrite Z.mod_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
   change (radix_value (square_reader_rho ax) mod feP=(@toZ (WordToZ 8) ax*1) mod feP).
   rewrite Z.mul_1_r.
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 assert (RD : radix_value (square_reader_rho ay) mod feP=@toZ (WordToZ 8) d mod feP).
 { unfold d;rewrite literal_multiply_numeric,C.jet_secp_curve_literal.literal_curve_cube_numeric,literal_fe_one256_value.
   rewrite Z.mod_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
   change (radix_value (square_reader_rho ay) mod feP=(@toZ (WordToZ 8) ay*1) mod feP).
   rewrite Z.mul_1_r.
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 f_equal.
 - f_equal;apply double_field_output_matches.
   + apply mixed_x_matches_literal;try apply square_reader_bounds;assumption.
   + apply mixed_y_matches_literal;try apply square_reader_bounds;assumption.
 - apply double_field_output_matches;apply mixed_z_matches_literal;try apply square_reader_bounds;try assumption.
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Theorem mixed_reader_outputs_literal (ax ay az bx byword : Ty.tySem (Word 8)) :
 let flag := bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 ((rescale_field_output (mixed_body_x_words flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)),
   rescale_field_output (mixed_body_y_words flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword))),
   rescale_field_output (mixed_body_z_words flag (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
      (square_reader_rho bx) (square_reader_rho byword)))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 cbv zeta;unfold mixed_body_x_words,mixed_body_y_words,mixed_body_z_words,bit_int.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:HInf.
 - change (((rescale_field_output (square_reader_rho bx),rescale_field_output (square_reader_rho byword)),
     rescale_field_output (C.jet_secp_point_set_bit.point_set_bit_words true))=
     @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword))).
   rewrite !mixed_reader_output,mixed_one_output;symmetry;apply literal_gej_ge_add_infinite.
   rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [u|u];destruct u;[discriminate HInf|reflexivity].
 - change (((rescale_field_output (mixed_finite_x_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
       (square_reader_rho bx) (square_reader_rho byword)),
    rescale_field_output (mixed_finite_y_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
       (square_reader_rho bx) (square_reader_rho byword))),
    rescale_field_output (mixed_finite_z_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
       (square_reader_rho bx) (square_reader_rho byword)))=
    @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword))).
   destruct (Z.eqb (radix_value (mixed_h_words (square_reader_rho ax) (square_reader_rho az) (square_reader_rho bx)) mod feP) 0) eqn:HH.
   + apply mixed_finite_zero_reader_outputs_literal;assumption.
   + apply mixed_nonzero_reader_outputs_literal;assumption.
Qed.

Theorem eval_mixed_literal (ax ay az bx byword : Ty.tySem (Word 8)) m bp ba :
 bp<>ba ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 (square_reader_rho ax)) -> fe_at m bp 40 (words5 (square_reader_rho ay)) ->
 fe_at m bp 80 (words5 (square_reader_rho az)) ->
 fe_at m ba 0 (words5 (square_reader_rho bx)) -> fe_at m ba 40 (words5 (square_reader_rho byword)) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 exists mf x y z,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
   (Vptr bp Ptrofs.zero :: Vptr bp Ptrofs.zero :: Vptr ba Ptrofs.zero :: Vlong Int64.zero :: nil) E0 mf Vundef /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 square_input_bounds x /\ square_input_bounds y /\ square_input_bounds z /\
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
   @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)) /\ lframe (fun b _=>b<>bp /\ b<>ba) m mf.
Proof.
 intros Sep FlagA FlagB X Y Z U V PF AF.
 destruct (eval_mixed_function (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
   (square_reader_rho bx) (square_reader_rho byword)
   (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))) m bp ba Sep
   (square_reader_positioned ax) (square_reader_positioned ay)
   (square_reader_bounds az) (square_reader_bounds bx) (square_reader_bounds byword)
   FlagA FlagB X Y Z U V PF AF)
   as (mf & HC & XF & YF & ZF & FlagF & PFF & AFF & BX & BY & BZ & Frame).
 exists mf;eexists;eexists;eexists.
 split;[exact HC|];split;[exact XF|];split;[exact YF|];split;[exact ZF|].
 split;[exact PFF|];split;[exact AFF|];split;[exact BX|];split;[exact BY|];split;[exact BZ|].
 split;[apply mixed_reader_outputs_literal|exact Frame].
Qed.

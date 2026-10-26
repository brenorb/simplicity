(** Original mixed addition on arbitrary matching loose X/Y coordinates.
    Normalization changes the machine temporaries, not their field residues.
    The equal-point branch still doubles the raw input point. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge C.jet_secp_field_mul_small
 C.jet_secp_field_weak_loose C.jet_secp_field_weak_tight C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_double_coordinate_numeric C.jet_secp_double_all_calls
 C.jet_secp_mixed_difference C.jet_secp_mixed_finite_prefix C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_finite_body C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail C.jet_secp_mixed_nonzero_literal
 C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_infinite_literal
 C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_body_loose C.jet_secp_mixed_function_loose
 C.jet_secp_gej_ge_equiv_dispatch C.jet_secp_add_literal C.jet_secp_add_literal_step
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize C.jet_secp_literal_gej_predicate
 C.jet_secp_literal_infinity C.jet_secp_rescale_literal C.jet_secp_square_execution
 C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_double_literal_bridge C.jet_secp_negate_literal_contract C.jet_secp_curve_literal C.jet_secp_double_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words weak_loose_words rescale_field_output
 literal_gej_ge_add literal_gej_is_infinity canonical_fe_is_zero canonical_fe_normalize literal_fe_multiply
 literal_fe_square literal_fe_cube literal_fe_one256 literal_fe_zero256
 literal_fe_add literal_fe_negate literal_fe_multiply_int literal_gej_double literal_gej_infinity.

Lemma mixed_xy_weak_residue x : square_input_bounds x ->
 radix_value (mixed_x_words true x) mod feP=radix_value x mod feP /\
 mul_small_input_bounds (mixed_x_words true x).
Proof. intro Bound;exact (weak_loose_numeric x (rescale_writer_bounds x Bound)). Qed.

Lemma mixed_xy_h_test x z u (a c b : Ty.tySem (Word 8)) :
 square_input_bounds x ->square_input_bounds z ->square_input_bounds u ->
 radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) b mod feP ->
 Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h a c b)).
Proof.
 intros BX BZ BU HX HZ HU;destruct (mixed_xy_weak_residue x BX) as [RX TightX].
 exact (mixed_h_residue_test (mixed_x_words true x) z u a c b TightX BZ BU (eq_trans RX HX) HZ HU).
Qed.

Lemma mixed_xy_i_test y z v (a c b : Ty.tySem (Word 8)) :
 square_input_bounds y ->square_input_bounds z ->square_input_bounds v ->
 radix_value y mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) b mod feP ->
 Z.eqb (radix_value (mixed_i_words (weak_loose_words y) z v) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i a c b)).
Proof.
 intros BY BZ BV HY HZ HV;destruct (mixed_xy_weak_residue y BY) as [RY TightY].
 exact (mixed_i_residue_test (weak_loose_words y) z v a c b TightY BZ BV (eq_trans RY HY) HZ HV).
Qed.

Theorem mixed_xy_nonzero_outputs_literal x y z u v (ax ay az bx byword : Ty.tySem (Word 8)) :
 square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 square_input_bounds u ->square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP) 0=false ->
 ((rescale_field_output (mixed_mode_finite_x_words true x y z u v),
   rescale_field_output (mixed_mode_finite_y_words true x y z u v)),
   rescale_field_output (mixed_mode_finite_z_words true x y z u v))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros BX BY BZ BU BV HX HY HZ HU HV HFin HH.
 destruct (mixed_xy_weak_residue x BX) as [RX TX].
 destruct (mixed_xy_weak_residue y BY) as [RY TY].
 assert (NX : square_input_bounds (mixed_x_words true x)) by (apply double_tight_loose;exact TX).
 assert (NY : square_input_bounds (weak_loose_words y)) by (apply double_tight_loose;exact TY).
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unit|unit];destruct unit;[reflexivity|discriminate HFin]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
   by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inl tt).
 { rewrite (mixed_xy_h_test x z u ax az bx BX BZ BU HX HZ HU) in HH.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [unit|unit];destruct unit;
     [reflexivity|discriminate HH]. }
 unfold mixed_mode_finite_x_words,mixed_mode_finite_y_words,mixed_mode_finite_z_words;rewrite HH.
 rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta;fold (mixed_literal_h ax az bx) (mixed_literal_i ay az byword);rewrite HZH.
 set (h := mixed_h_words (mixed_x_words true x) z u).
 set (i := mixed_i_words (weak_loose_words y) z v).
 set (a := mixed_literal_h ax az bx);set (b := mixed_literal_i ay az byword).
 set (c := @literal_fe_multiply Alg.CoreFunSem (ax,@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 set (d := @literal_fe_multiply Alg.CoreFunSem (ay,@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))).
 change (((rescale_field_output (mixed_nonzero_x_words h i (mixed_x_words true x)),
   rescale_field_output (mixed_nonzero_y_words h i (mixed_x_words true x) (weak_loose_words y))),
   rescale_field_output (point_mul_words z h))=
   ((mixed_literal_rx a b c,mixed_literal_ry a b c d),mixed_literal_rz a az)).
 assert (BH : square_input_bounds h).
 { unfold h,mixed_h_words;apply (proj2 (mixed_difference_numeric _ _ TX
     (double_mul_tight _ _ BU (double_tight_loose _ (double_square_tight _ BZ))))). }
 assert (BI : square_input_bounds i).
 { unfold i,mixed_i_words;refine (proj2 (mixed_difference_numeric _ _ _ TY)).
   apply double_mul_tight;[|exact BZ].
   apply double_tight_loose;apply double_mul_tight;[exact BV|].
   apply double_tight_loose;apply double_square_tight;exact BZ. }
 assert (RH : radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP).
 { unfold h,a;rewrite mixed_literal_h_numeric.
   change (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP=
     (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az) mod feP) mod feP).
   rewrite Zminus_mod_idemp_r.
   replace (0-(@toZ (WordToZ 8) ax-@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az)) with
     (@toZ (WordToZ 8) bx*@toZ (WordToZ 8) az*@toZ (WordToZ 8) az-@toZ (WordToZ 8) ax) by ring.
   exact (mixed_h_residue _ _ _ _ _ _ TX BZ BU (eq_trans RX HX) HZ HU). }
 assert (RI : radix_value i mod feP=@toZ (WordToZ 8) b mod feP).
 { unfold i,b;rewrite mixed_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
   exact (mixed_i_residue _ _ _ _ _ _ TY BZ BV (eq_trans RY HY) HZ HV). }
 assert (RC : radix_value (mixed_x_words true x) mod feP=@toZ (WordToZ 8) c mod feP).
 { unfold c;rewrite literal_multiply_numeric,literal_square_numeric,literal_fe_one256_value.
   rewrite Z.mod_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
   change (radix_value (mixed_x_words true x) mod feP=(@toZ (WordToZ 8) ax*1) mod feP).
   rewrite Z.mul_1_r;exact (eq_trans RX HX). }
 assert (RD : radix_value (weak_loose_words y) mod feP=@toZ (WordToZ 8) d mod feP).
 { unfold d;rewrite literal_multiply_numeric,literal_curve_cube_numeric,literal_fe_one256_value.
   rewrite Z.mod_mod,Z.mul_mod_idemp_r by (unfold feP,feR;lia).
   change (radix_value (weak_loose_words y) mod feP=(@toZ (WordToZ 8) ay*1) mod feP).
   rewrite Z.mul_1_r;exact (eq_trans RY HY). }
 f_equal.
 - f_equal;apply double_field_output_matches.
   + apply mixed_x_matches_literal;assumption.
   + apply mixed_y_matches_literal;assumption.
 - apply double_field_output_matches;apply mixed_z_matches_literal;assumption.
Qed.

Theorem mixed_xy_zero_outputs_literal x y z u v (ax ay az bx byword : Ty.tySem (Word 8)) :
 square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 square_input_bounds u ->square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP) 0=true ->
 ((rescale_field_output (mixed_mode_finite_x_words true x y z u v),
   rescale_field_output (mixed_mode_finite_y_words true x y z u v)),
   rescale_field_output (mixed_mode_finite_z_words true x y z u v))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros BX BY BZ BU BV HX HY HZ HU HV HFin HH.
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unit|unit];destruct unit;[reflexivity|discriminate HFin]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
   by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
 assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt).
 { rewrite (mixed_xy_h_test x z u ax az bx BX BZ BU HX HZ HU) in HH.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [unit|unit];destruct unit;
     [discriminate HH|reflexivity]. }
 unfold mixed_mode_finite_x_words,mixed_mode_finite_y_words,mixed_mode_finite_z_words;rewrite HH.
 unfold mixed_zero_words;rewrite (mixed_xy_i_test y z v ay az byword BY BZ BV HY HZ HV).
 rewrite literal_gej_ge_add_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta;fold (mixed_literal_h ax az bx) (mixed_literal_i ay az byword);rewrite HZH.
 destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)) as [unit|unit];destruct unit;cbn [Bit.toBool].
 - change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
     rescale_field_output (fun _ : nat=>Int64.zero))=
     ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
   assert (Zero : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
     by exact zero_field_writer_literal_output.
   rewrite Zero;reflexivity.
 - rewrite literal_gej_double_step,literal_gej_is_infinity_value,HFin.
   exact (double_body_writer_outputs_literal x y z ax ay az BX BY BZ HX HY HZ).
Qed.

Lemma mixed_xy_output_normalize w (a : Ty.tySem (Word 8)) :
 radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
 rescale_field_output w=@canonical_fe_normalize Alg.CoreFunSem a.
Proof.
 intro Value;apply (toZ_injective (WordToZ 8)).
 rewrite rescale_field_output_value,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model,
   field_prime_matches_normalizer;exact Value.
Qed.

Theorem mixed_xy_outputs_literal x y z u v (ax ay az bx byword : Ty.tySem (Word 8)) :
 square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 square_input_bounds u ->square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 let flag:=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 ((rescale_field_output (mixed_mode_body_x_words true flag x y z u v),
   rescale_field_output (mixed_mode_body_y_words true flag x y z u v)),
   rescale_field_output (mixed_mode_body_z_words true flag x y z u v))=
 @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)).
Proof.
 intros BX BY BZ BU BV HX HY HZ HU HV;cbv zeta.
 unfold mixed_mode_body_x_words,mixed_mode_body_y_words,mixed_mode_body_z_words,bit_int.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:HInf.
 - change (((rescale_field_output u,rescale_field_output v),
     rescale_field_output (C.jet_secp_point_set_bit.point_set_bit_words true))=
     @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword))).
   rewrite (mixed_xy_output_normalize u bx HU),(mixed_xy_output_normalize v byword HV),mixed_one_output.
   symmetry;apply literal_gej_ge_add_infinite;rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [unit|unit];destruct unit;[discriminate HInf|reflexivity].
 - change (((rescale_field_output (mixed_mode_finite_x_words true x y z u v),
     rescale_field_output (mixed_mode_finite_y_words true x y z u v)),
     rescale_field_output (mixed_mode_finite_z_words true x y z u v))=
     @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword))).
   destruct (Z.eqb (radix_value (mixed_h_words (mixed_x_words true x) z u) mod feP) 0) eqn:HH.
   + exact (mixed_xy_zero_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV HInf HH).
   + exact (mixed_xy_nonzero_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV HInf HH).
Qed.

Theorem eval_mixed_xy_literal x y z u v (ax ay az bx byword : Ty.tySem (Word 8)) m bp ba :
 bp<>ba ->square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 square_input_bounds u ->square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) ->fe_at m ba 40 (words5 v) ->
 Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m ba 0 88 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
   (Vptr bp Ptrofs.zero::Vptr bp Ptrofs.zero::Vptr ba Ptrofs.zero::Vlong Int64.zero::nil) E0 mf Vundef /\
 fe_at mf bp 0 (words5 ox) /\fe_at mf bp 40 (words5 oy) /\fe_at mf bp 80 (words5 oz) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf ba 0 88 Cur Freeable /\
 square_input_bounds ox /\square_input_bounds oy /\square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)) /\
 lframe (fun b _=>b<>bp /\b<>ba) m mf.
Proof.
 intros Sep BX BY BZ BU BV HX HY HZ HU HV FlagA FlagB X Y Z U V PF AF.
 destruct (eval_mixed_function_xy x y z u v
   (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))) m bp ba
   Sep BX BY BZ BU BV FlagA FlagB X Y Z U V PF AF)
   as (mf & Call & XO & YO & ZO & FlagO & PFO & AFO & BXO & BYO & BZO & Frame).
 exists mf;eexists;eexists;eexists.
 split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];
 split;[exact PFO|];split;[exact AFO|];split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
 - exact (mixed_xy_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV).
 - exact Frame.
Qed.

Lemma mixed_xy_output_residue w :
 radix_value w mod feP=@toZ (WordToZ 8) (rescale_field_output w) mod feP.
Proof.
 rewrite rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia).
 reflexivity.
Qed.

(** The generator initializes the projective Z to one, without a reader. *)
Theorem mixed_xy_affine_outputs_literal x y u v :
 square_input_bounds x ->square_input_bounds y ->square_input_bounds u ->square_input_bounds v ->
 let z:=C.jet_secp_point_set_bit.point_set_bit_words true in
 ((rescale_field_output (mixed_mode_body_x_words true Int.zero x y z u v),
   rescale_field_output (mixed_mode_body_y_words true Int.zero x y z u v)),
   rescale_field_output (mixed_mode_body_z_words true Int.zero x y z u v))=
 @literal_gej_ge_add Alg.CoreFunSem
   (((rescale_field_output x,rescale_field_output y),@literal_fe_one256 Alg.CoreFunSem tt),
     (rescale_field_output u,rescale_field_output v)).
Proof.
 intros BX BY BU BV;cbv zeta.
 assert (One : radix_value (C.jet_secp_point_set_bit.point_set_bit_words true) mod feP=
   @toZ (WordToZ 8) (@literal_fe_one256 Alg.CoreFunSem tt) mod feP).
 { rewrite <-field_prime_matches_normalizer,<-rescale_field_output_value,mixed_one_output,
     canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model;reflexivity. }
 pose proof (mixed_xy_outputs_literal x y (C.jet_secp_point_set_bit.point_set_bit_words true) u v
   (rescale_field_output x) (rescale_field_output y) (@literal_fe_one256 Alg.CoreFunSem tt)
   (rescale_field_output u) (rescale_field_output v) BX BY mixed_one_bounds BU BV
   (mixed_xy_output_residue x) (mixed_xy_output_residue y) One (mixed_xy_output_residue u) (mixed_xy_output_residue v)) as Result.
 cbv zeta in Result;rewrite mixed_literal_one_finite in Result;exact Result.
Qed.

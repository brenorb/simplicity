(** Finite projective machine outputs, including both H/I dispatches, decoded
    by the original writer against the complete fixed literal addition tree. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge C.jet_secp_point_mul_storage
 C.jet_secp_point_mul_numeric C.jet_secp_curve_mul C.jet_secp_field_mul_small C.jet_secp_double_coordinate_numeric
 C.jet_secp_gej_add_finite_difference C.jet_secp_gej_add_finite_body C.jet_secp_gej_add_finite_literal C.jet_secp_gej_add_dispatch_literal
 C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail C.jet_secp_mixed_dispatch_literal
 C.jet_secp_mixed_nonzero_literal C.jet_secp_double_all_calls C.jet_secp_double_literal_bridge
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_canonical_normalize
 C.jet_secp_add_literal C.jet_secp_add_literal_step C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity
 C.jet_secp_square_execution C.jet_secp_multiply_literal_spec C.jet_secp_literal_add_program
 C.jet_secp_literal_add_numeric C.jet_secp_negate_literal_contract C.jet_secp_curve_literal C.jet_secp_double_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words rescale_field_output literal_gej_add literal_gej_is_infinity
 canonical_fe_is_zero literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity.

Lemma gej_add_h_matches_literal mx mz mu mw (a c b d : Ty.tySem (Word 8)) :
 square_input_bounds mx ->
 square_input_bounds mz ->
 square_input_bounds mu ->
 square_input_bounds mw ->
 radix_value mx mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value mz mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value mu mod feP=@toZ (WordToZ 8) b mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) d mod feP ->
 radix_value (gej_add_h_words mx mz mu mw) mod feP=
 (-@toZ (WordToZ 8) (gej_add_literal_h a c b d)) mod feP.
Proof.
 intros Bmx Bmz Bmu Bmw Rmx Rmz Rmu Rmw.
 rewrite gej_add_literal_h_numeric.
 change (radix_value (gej_add_h_words mx mz mu mw) mod feP=
   (0-(@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
   @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c) mod feP) mod feP).
 rewrite Zminus_mod_idemp_r.
 replace (0-(@toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d-
   @toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) with
  (@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c-
   @toZ (WordToZ 8) a*@toZ (WordToZ 8) d*@toZ (WordToZ 8) d) by ring.
 apply gej_add_h_residue;assumption.
Qed.

Lemma gej_add_i_matches_literal my mz mv mw (a c b d : Ty.tySem (Word 8)) :
 square_input_bounds my ->
 square_input_bounds mz ->
 square_input_bounds mv ->
 square_input_bounds mw ->
 radix_value my mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value mz mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value mv mod feP=@toZ (WordToZ 8) b mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) d mod feP ->
 radix_value (gej_add_i_words my mz mv mw) mod feP=
 @toZ (WordToZ 8) (gej_add_literal_i a c b d) mod feP.
Proof.
 intros Bmy Bmz Bmv Bmw Rmy Rmz Rmv Rmw.
 rewrite gej_add_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply gej_add_i_residue;assumption.
Qed.

Lemma gej_add_u_matches_literal mx mw (a d : Ty.tySem (Word 8)) :
 square_input_bounds mx ->
 square_input_bounds mw ->
 radix_value mx mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) d mod feP ->
 radix_value (gej_add_u1_words mx mw) mod feP=
 @toZ (WordToZ 8) (gej_add_literal_u a d) mod feP.
Proof.
 intros Bmx Bmw Rmx Rmw.
 rewrite gej_add_literal_u_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply gej_add_u_residue;assumption.
Qed.

Lemma gej_add_s_matches_literal my mw (a d : Ty.tySem (Word 8)) :
 square_input_bounds my ->
 square_input_bounds mw ->
 radix_value my mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) d mod feP ->
 radix_value (gej_add_s1_words my mw) mod feP=
 @toZ (WordToZ 8) (gej_add_literal_s a d) mod feP.
Proof.
 intros Bmy Bmw Rmy Rmw.
 rewrite gej_add_literal_s_numeric,Z.mod_mod by (unfold feP,feR;lia).
 apply gej_add_s_residue;assumption.
Qed.

Theorem gej_add_finite_outputs_literal mx my mz mu mv mw (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 square_input_bounds mx ->
 square_input_bounds my ->
 square_input_bounds mz ->
 square_input_bounds mu ->
 square_input_bounds mv ->
 square_input_bounds mw ->
 radix_value mx mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value my mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value mz mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value mu mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value mv mod feP=@toZ (WordToZ 8) byword mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) bz mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)=Datatypes.false ->
 ((rescale_field_output (gej_add_finite_x_words mx my mz
      mu mv mw),
   rescale_field_output (gej_add_finite_y_words mx my mz
      mu mv mw)),
   rescale_field_output (gej_add_finite_z_words mx my mz
      mu mv mw))=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)).
Proof.
 intros BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FinA FinB.
 pose proof (gej_add_h_matches_literal mx mz mu mw ax az bx bz BMX BMZ BMU BMW RMX RMZ RMU RMW) as MH.
 pose proof (gej_add_i_matches_literal my mz mv mw ay az byword bz BMY BMZ BMV BMW RMY RMZ RMV RMW) as MI.
 pose proof (gej_add_u_matches_literal mx mw ax bz BMX BMW RMX RMW) as MUval.
 pose proof (gej_add_s_matches_literal my mw ay bz BMY BMW RMY RMW) as MSval.
 assert (HBool : Z.eqb (radix_value (gej_add_h_words mx mz mu mw) mod feP) 0=
   Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz))).
 { rewrite MH,literal_curve_zero_numeric;apply mixed_negated_zero_test. }
 assert (IBool : Z.eqb (radix_value (gej_add_i_words my mz mv mw) mod feP) 0=
   Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_i ay az byword bz))).
 { rewrite MI,literal_curve_zero_numeric;reflexivity. }
 assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[reflexivity|discriminate FinA]. }
 assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),bz)=inl tt).
 { rewrite literal_gej_is_infinity_value.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem bz) as [[] | []];[reflexivity|discriminate FinB]. }
 rewrite gej_add_literal_expansion,literal_gej_add_finite_step by assumption.
 cbv zeta.
 fold (gej_add_literal_u ax bz) (gej_add_literal_u (@literal_fe_negate Alg.CoreFunSem bx) az)
   (gej_add_literal_s ay bz) (gej_add_literal_s (@literal_fe_negate Alg.CoreFunSem byword) az).
 fold (gej_add_literal_h ax az bx bz) (gej_add_literal_i ay az byword bz).
 unfold gej_add_finite_x_words,gej_add_finite_y_words,gej_add_finite_z_words.
 destruct (Z.eqb (radix_value (gej_add_h_words mx mz
   mu mw) mod feP) 0) eqn:HH.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)=inr tt).
   { pose proof HBool as HHBool.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)) as [[] | []];
       [discriminate HHBool|reflexivity]. }
   rewrite HZH;unfold mixed_zero_words;rewrite IBool.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_i ay az byword bz)) as [[] | []] eqn:HI;
     cbn [Bit.toBool].
   + change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
       rescale_field_output (fun _ : nat=>Int64.zero))=
       ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
     assert (Zero : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
       by exact zero_field_writer_literal_output.
     rewrite Zero;reflexivity.
   + rewrite literal_gej_double_step,literal_gej_is_infinity_value,FinA.
     apply double_body_writer_outputs_literal;assumption.
 - assert (HZH : @canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)=inl tt).
   { pose proof HBool as HHBool.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem (gej_add_literal_h ax az bx bz)) as [[] | []];
       [reflexivity|discriminate HHBool]. }
   rewrite HZH.
   set (h := gej_add_h_words mx mz mu mw).
   set (i := gej_add_i_words my mz mv mw).
   set (u := gej_add_u1_words mx mw).
   set (s := gej_add_s1_words my mw).
   set (a := gej_add_literal_h ax az bx bz);set (b := gej_add_literal_i ay az byword bz).
   set (c := gej_add_literal_u ax bz);set (d := gej_add_literal_s ay bz).
   change (((rescale_field_output (mixed_nonzero_x_words h i u),rescale_field_output (mixed_nonzero_y_words h i u s)),
     rescale_field_output (point_mul_words mz (point_mul_words h mw)))=
     ((mixed_literal_rx a b c,mixed_literal_ry a b c d),gej_add_literal_rz a az bz)).
   assert (BH : square_input_bounds h) by (unfold h;apply gej_add_h_bounds;assumption).
   assert (BI : square_input_bounds i) by (unfold i;apply gej_add_i_bounds;assumption).
   assert (BU : square_input_bounds u).
   { unfold u,gej_add_u1_words;apply double_tight_loose;apply double_mul_tight;[exact BMX|].
     apply double_tight_loose;apply double_square_tight;exact BMW. }
   assert (BS : square_input_bounds s).
   { unfold s,gej_add_s1_words;apply double_tight_loose;apply double_mul_tight;[|exact BMW].
     apply double_tight_loose;apply double_mul_tight;[exact BMY|].
     apply double_tight_loose;apply double_square_tight;exact BMW. }
   assert (RH : radix_value h mod feP=(-@toZ (WordToZ 8) a) mod feP) by exact MH.
   assert (RI : radix_value i mod feP=@toZ (WordToZ 8) b mod feP) by exact MI.
   assert (RU : radix_value u mod feP=@toZ (WordToZ 8) c mod feP) by exact MUval.
   assert (RS : radix_value s mod feP=@toZ (WordToZ 8) d mod feP) by exact MSval.
   f_equal.
   + f_equal;apply double_field_output_matches.
     * apply mixed_x_matches_literal;assumption.
     * apply mixed_y_matches_literal;assumption.
   + apply double_field_output_matches;apply gej_add_z_matches_literal;assumption.
Qed.

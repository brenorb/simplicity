(** The actual decompressor selects the unique normalized even curve point. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_even_y_unique
 C.jet_secp_affine_word_valid C.jet_secp_decompress_literal C.jet_secp_decompress_sign
 C.jet_secp_rescale_literal C.jet_secp_root_literal C.jet_secp_root_chain_numeric C.jet_secp_curve_literal
 C.jet_secp_literal_add_numeric C.jet_secp_literal_add_program C.jet_secp_canonical_normalize
 C.jet_secp_canonical_odd C.jet_secp_negate_literal_contract C.jet_secp_swu_root_power.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_is_odd literal_fe_negate literal_decompress literal_y_from_x
 literal_fe_square_root literal_fe_add literal_fe_cube toZ literal_root_candidate.
Definition secp_even_ordinate (y:Ty.tySem (Word 8)):=
 if Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y) then @literal_fe_negate Alg.CoreFunSem y else y.
Lemma secp_even_ordinate_properties (y:Ty.tySem (Word 8)):
 0<=@toZ (WordToZ 8) y<feP ->
 0<=@toZ (WordToZ 8) (secp_even_ordinate y)<feP /\
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem (secp_even_ordinate y))=Datatypes.false.
Proof.
 intro Range;unfold secp_even_ordinate.
 destruct (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) eqn:Odd.
 - assert (Nonzero:@toZ (WordToZ 8) y<>0).
   { rewrite canonical_fe_is_odd_numeric,(secp_normalize_bounded_word y Range) in Odd.
     intro Zero;rewrite Zero in Odd;discriminate. }
   split.
   + rewrite literal_curve_negate_numeric;apply Z.mod_pos_bound;pose proof secp_group_field_positive;lia.
   + exact (eq_trans (secp_field_negate_odd y ltac:(clear -Range Nonzero;lia)) (f_equal negb Odd)).
 - split;[exact Range|exact Odd].
Qed.
Lemma secp_even_decompress_of_root (x y:Ty.tySem (Word 8)):
 @literal_y_from_x Alg.CoreFunSem x=inr y ->
 @literal_decompress Alg.CoreFunSem (inl tt,x)=
 inr (@canonical_fe_normalize Alg.CoreFunSem x,secp_even_ordinate y).
Proof.
 intro Root;rewrite literal_decompress_step,Root.
 unfold secp_even_ordinate;cbn [Bit.toBool];destruct (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y));reflexivity.
Qed.
Theorem secp_even_decompress_complete (x y:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true ->
 0<=@toZ (WordToZ 8) x<feP ->0<=@toZ (WordToZ 8) y<feP ->
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)=Datatypes.false ->
 @literal_decompress Alg.CoreFunSem (inl tt,x)=inr (x,y).
Proof.
 intros Curve RangeX RangeY Even.
 set (rad:=@literal_fe_add Alg.CoreFunSem (curve_seven_word,@literal_fe_cube Alg.CoreFunSem x)).
 assert (Square:@toZ (WordToZ 8) rad mod feP=(@toZ (WordToZ 8) y*@toZ (WordToZ 8) y) mod feP).
 { unfold rad;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,curve_seven_value,
    literal_curve_cube_numeric,Z.mod_mod,Z.add_mod_idemp_r by (pose proof secp_group_field_positive;lia).
   rewrite literal_ge_curve_numeric in Curve;apply Z.eqb_eq in Curve.
   rewrite Z.add_comm;symmetry;exact Curve. }
 assert (Root:@literal_y_from_x Alg.CoreFunSem x=inr (literal_root_candidate rad)).
 { rewrite literal_y_from_x_step;exact (swu_literal_root_success_on_square rad (@toZ (WordToZ 8) y) Square). }
 pose proof (secp_even_decompress_of_root x _ Root) as Output.
 rewrite (secp_normalize_bounded_word x RangeX) in Output.
 pose proof (decompress_y_from_x_range x _ Root) as RootRange.
 destruct (secp_even_ordinate_properties _ RootRange) as [SelectedRange SelectedEven].
 pose proof (secp_decompress_curve x (inl tt) _ Output) as SelectedCurve.
 pose proof (secp_even_y_unique x y _ Curve SelectedCurve RangeY SelectedRange Even SelectedEven) as Equal.
 exact (eq_trans Output (f_equal (fun word:Ty.tySem (Word 8)=>inr (x,word)) (eq_sym Equal))).
Qed.
Theorem secp_even_decompress_properties (x ax ay:Ty.tySem (Word 8)):
 @literal_decompress Alg.CoreFunSem (inl tt,x)=inr (ax,ay) ->
 ax=@canonical_fe_normalize Alg.CoreFunSem x /\
 0<=@toZ (WordToZ 8) ay<feP /\
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem ay)=Datatypes.false.
Proof.
 intro Output;pose proof Output as Expanded;rewrite literal_decompress_step in Expanded.
 destruct (@literal_y_from_x Alg.CoreFunSem x) as [u|root] eqn:Root;[discriminate|].
 pose proof (eq_trans (eq_sym Output) (secp_even_decompress_of_root x root Root)) as Coordinates.
 injection Coordinates as X Y;split;[exact X|].
 rewrite Y;apply secp_even_ordinate_properties;exact (decompress_y_from_x_range x root Root).
Qed.
Theorem secp_even_decompress_iff (x y:Ty.tySem (Word 8)):
 0<=@toZ (WordToZ 8) x<feP ->0<=@toZ (WordToZ 8) y<feP ->
 (@literal_decompress Alg.CoreFunSem (inl tt,x)=inr (x,y) <->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true /\
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)=Datatypes.false).
Proof.
 intros RangeX RangeY;split.
 - intro Output;split.
   + exact (secp_decompress_curve x (inl tt) (x,y) Output).
   + exact (proj2 (proj2 (secp_even_decompress_properties x x y Output))).
 - intros [Curve Even];apply secp_even_decompress_complete;assumption.
Qed.
Corollary secp_even_decompress_failure (x y:Ty.tySem (Word 8)):
 @literal_decompress Alg.CoreFunSem (inl tt,x)=inl tt ->
 0<=@toZ (WordToZ 8) x<feP ->0<=@toZ (WordToZ 8) y<feP ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true ->
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)<>Datatypes.false.
Proof.
 intros Failed RangeX RangeY Curve Even.
 pose proof (secp_even_decompress_complete x y Curve RangeX RangeY Even) as Succeeded.
 rewrite Failed in Succeeded;discriminate.
Qed.

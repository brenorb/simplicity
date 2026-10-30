(** Establish group representations from the existing literal curve test. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_curve_group_sign C.jet_secp_field_word_group C.jet_secp_generator_base_group
 C.jet_secp_jacobian_group C.jet_secp_jacobian_affine_group C.jet_secp_jacobian_word_group
 C.jet_secp_table_pass2_group C.jet_secp_curve_literal C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_affine_word_valid_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Lemma secp_affine_curve_of_literal (x y:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true ->
 SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_field_word y) 2=
 GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_field_word x) 3)
  (GZnZ.mul feP (GZnZ.zero feP) (secp_field_word x))) secp_group_seven.
Proof.
 rewrite literal_ge_curve_numeric;intro Valid;apply Z.eqb_eq in Valid.
 apply GZnZ.zirr.
 cbn [SMain.pow GZnZ.val GZnZ.mul GZnZ.add GZnZ.zero GZnZ.one secp_field_word secp_field_integer secp_group_seven].
 rewrite !Z.mul_mod_idemp_l,!Z.mul_mod_idemp_r by (pose proof secp_group_field_positive;lia).
 rewrite Z.mul_0_l,Z.mod_0_l,Z.add_0_r by (pose proof secp_group_field_positive;lia).
 rewrite Z.mul_assoc.
 rewrite Z.mul_mod_idemp_r,!Z.add_mod_idemp_l by (pose proof secp_group_field_positive;lia).
 exact Valid.
Qed.
Theorem secp_affine_literal_represented (x y:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true ->
 exists p:secp_group_point,secp_affine_word_rep (GZnZ.one feP) (x,y) p.
Proof.
 intro Valid;exists (SMain.curve_elt _ _ _ _ _ _ _ (secp_affine_curve_of_literal x y Valid)).
 apply secp_affine_unit_group.
Qed.
Lemma secp_jacobian_word_rep_unique c point (p q:secp_group_point):
 secp_jacobian_word_rep c point p ->secp_jacobian_word_rep c point q ->p=q.
Proof.
 intros [CP VP] [CQ VQ];rewrite <-VP,<-VQ.
 apply secp_jacobian_group_value_ext;reflexivity.
Qed.
Lemma secp_affine_word_rep_finite (x y:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_affine_word_rep (GZnZ.one feP) (x,y) p ->p<>secp_group_infinity.
Proof.
 intros [Curve Value] Infinity.
 cbn [secp_jacobian_word_fields fst snd] in Curve,Value.
 assert (ZOne:GZnZ.mul feP (GZnZ.one feP) (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt))=GZnZ.one feP).
 { rewrite secp_field_word_one;ring. }
 rewrite <-Value in Infinity.
 apply (proj1 (secp_jacobian_group_infinity_iff _ _ _ Curve)) in Infinity.
 rewrite ZOne in Infinity;discriminate.
Qed.
Require Import C.jet_toZ C.jet_secp_canonical_normalize.
Lemma secp_field_word_equal_normalized (x y:Ty.tySem (Word 8)):
 secp_field_word x=secp_field_word y ->
 @canonical_fe_normalize Alg.CoreFunSem x=@canonical_fe_normalize Alg.CoreFunSem y.
Proof.
 intro Equal;apply (toZ_injective (WordToZ 8)).
 rewrite !canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
 exact (f_equal (GZnZ.val feP) Equal).
Qed.
Require Import C.jet_secp_decompress_literal C.jet_secp_decompress_readback
 C.jet_secp_root_function_literal C.jet_secp_square_spec_bridge.
Lemma secp_decompress_curve (x:Ty.tySem (Word 8)) (odd:Ty.tySem Bit)
 (ap:Ty.tySem (Ty.Prod (Word 8) (Word 8))):
 @literal_decompress Alg.CoreFunSem (odd,x)=inr ap ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem ap)=Datatypes.true.
Proof.
 intro Success;exact (decompress_literal_point_curve (square_reader_rho x) x odd ap (root_reader_matches x) Success).
Qed.
Theorem secp_decompress_represented (x:Ty.tySem (Word 8)) (odd:Ty.tySem Bit)
 (ax ay:Ty.tySem (Word 8)):
 @literal_decompress Alg.CoreFunSem (odd,x)=inr (ax,ay) ->
 exists p:secp_group_point,secp_affine_word_rep (GZnZ.one feP) (ax,ay) p /\p<>secp_group_infinity.
Proof.
 intro Success;destruct (secp_affine_literal_represented ax ay (secp_decompress_curve x odd (ax,ay) Success))
 as [p Represented].
 exists p;split;[exact Represented|exact (secp_affine_word_rep_finite ax ay p Represented)].
Qed.
Definition secp_group_point_x (p:secp_group_point):secp_group_field:=
 match p with SMain.inf_elt _ _ _ _ _=>GZnZ.zero feP|SMain.curve_elt _ _ _ _ _ x _ _=>x end.
Definition secp_group_point_y (p:secp_group_point):secp_group_field:=
 match p with SMain.inf_elt _ _ _ _ _=>GZnZ.zero feP|SMain.curve_elt _ _ _ _ _ _ y _=>y end.
Lemma secp_affine_word_rep_coordinates (x y:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_affine_word_rep (GZnZ.one feP) (x,y) p ->
 secp_group_point_x p=secp_field_word x /\secp_group_point_y p=secp_field_word y.
Proof.
 intros [Curve Value].
 cbn [secp_jacobian_word_fields fst snd] in Curve,Value.
 set (z:=GZnZ.mul feP (GZnZ.one feP) (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt))) in *.
 assert (Unit:z=GZnZ.one feP).
 { unfold z;rewrite secp_field_word_one;ring. }
 assert (Nonzero:z<>GZnZ.zero feP) by (rewrite Unit;discriminate).
 rewrite <-Value,(secp_jacobian_affine_value _ _ _ Curve Nonzero).
 unfold secp_group_point_x,secp_group_point_y;rewrite Unit;split;unfold secp_group_field;field;discriminate.
Qed.
Lemma secp_affine_word_same_point (x y u v:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_affine_word_rep (GZnZ.one feP) (x,y) p ->
 secp_affine_word_rep (GZnZ.one feP) (u,v) p ->
 @canonical_fe_normalize Alg.CoreFunSem x=@canonical_fe_normalize Alg.CoreFunSem u /\
 @canonical_fe_normalize Alg.CoreFunSem y=@canonical_fe_normalize Alg.CoreFunSem v.
Proof.
 intros Left Right.
 destruct (secp_affine_word_rep_coordinates x y p Left) as [LX LY].
 destruct (secp_affine_word_rep_coordinates u v p Right) as [RX RY].
 split;apply secp_field_word_equal_normalized;congruence.
Qed.

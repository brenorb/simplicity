(** Connect the native tweak payload to literal generate/add/normalize. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_power
 C.jet_secp_lookup5_group C.jet_secp_signed_group_action C.jet_secp_generate_group C.jet_secp_field_word_group
 C.jet_secp_jacobian_word_group C.jet_secp_jacobian_mixed_word_group C.jet_secp_table_pass2_group
 C.jet_secp_affine_word_valid C.jet_secp_strauss_complete_program C.jet_secp_strauss_body_group C.jet_secp_norm_group C.jet_secp_even_x_test
 C.jet_secp_curve_literal C.jet_secp_literal_gej_predicate C.jet_secp_literal_add_program C.jet_secp_gej_norm_literal
 C.jet_secp_canonical_scalar C.jet_secp_eckey_tweak_prepare C.jet_secp_eckey_tweak_function
 C.jet_secp_tweak_bytes_function C.jet_secp_xonly_tweak_function C.jet_secp_ge_storage_body
 C.jet_secp_multiply_normalize_bridge C.jet_secp_fe_inv_prefix C.jet_secp_rescale_literal C.jet_secp_multiply_finish_product
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_secp_pubkey_load_coordinates.
Require Import C.jet_secp_scalar_table_literal C.jet_secp_add_literal C.jet_secp_tweak_group C.jet_secp_linear_check_group C.jet_secp_generate_program
 C.jet_secp_generator_complete_group C.jet_secp_strauss_group C.jet_secp_gej_norm_branch
 C.jet_secp_canonical_normalize C.jet_secp_even_y_unique.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_strauss_body literal_gej_norm literal_gej_normalize literal_gej_is_infinity
 literal_gej_ge_add literal_generate secp_field_word secp_group_signed_power SMain.add canonical_scalar_normalize.
Lemma literal_gej_normalize_flag_value (point:Ty.tySem literal_table_gej):
 @literal_gej_normalize Alg.CoreFunSem point=
 if Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point) then inl tt else inr (@literal_gej_norm Alg.CoreFunSem point).
Proof. destruct point as [[x y] z];rewrite literal_gej_normalize_value,literal_gej_is_infinity_value;reflexivity. Qed.
Lemma secp_noninfinite_norm_group (point:Ty.tySem literal_table_gej) (p:secp_group_point):
 Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point)=Datatypes.false ->
 secp_jacobian_word_rep (GZnZ.one feP) point p ->
 secp_affine_word_rep (GZnZ.one feP) (@literal_gej_norm Alg.CoreFunSem point) p.
Proof.
 destruct point as [[x y] z];intros Finite Represented;apply secp_literal_gej_norm_group;[|exact Represented].
 intro Zero;apply (proj2 (secp_field_word_flag_true z)) in Zero.
 rewrite literal_gej_is_infinity_value in Finite;congruence.
Qed.
Theorem secp_gej_normalize_same_group (a b:Ty.tySem literal_table_gej) (p:secp_group_point):
 secp_jacobian_word_rep (GZnZ.one feP) a p ->secp_jacobian_word_rep (GZnZ.one feP) b p ->
 @literal_gej_normalize Alg.CoreFunSem a=@literal_gej_normalize Alg.CoreFunSem b.
Proof.
 intros A B;pose proof (secp_jacobian_word_infinity a p A) as IA;pose proof (secp_jacobian_word_infinity b p B) as IB.
 assert (Flags:Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem a)=Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem b)).
 { destruct (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem a)) eqn:FA,
   (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem b)) eqn:FB;try reflexivity.
   - exfalso;pose proof (proj1 IA eq_refl) as P;pose proof (proj2 IB P);discriminate.
   - exfalso;pose proof (proj1 IB eq_refl) as P;pose proof (proj2 IA P);discriminate. }
 rewrite !literal_gej_normalize_flag_value,<-Flags.
 destruct (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem a)) eqn:Finite;[reflexivity|].
 assert (FiniteB:Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem b)=Datatypes.false) by congruence.
 pose proof (secp_noninfinite_norm_group a p Finite A) as NA.
 pose proof (secp_noninfinite_norm_group b p FiniteB B) as NB.
 assert (RA:let xy:=@literal_gej_norm Alg.CoreFunSem a in
  0<=@toZ (WordToZ 8) (fst xy)<feP /\0<=@toZ (WordToZ 8) (snd xy)<feP).
 { destruct a as [[x y] z];apply secp_gej_norm_ranges. }
 assert (RB:let xy:=@literal_gej_norm Alg.CoreFunSem b in
  0<=@toZ (WordToZ 8) (fst xy)<feP /\0<=@toZ (WordToZ 8) (snd xy)<feP).
 { destruct b as [[x y] z];apply secp_gej_norm_ranges. }
 destruct (@literal_gej_norm Alg.CoreFunSem a) as [ax ay].
 destruct (@literal_gej_norm Alg.CoreFunSem b) as [bx byword].
 destruct RA as [RAX RAY];destruct RB as [RBX RBY].
 destruct (secp_affine_word_same_point ax ay bx byword p NA NB) as [X Y].
 rewrite !secp_normalize_bounded_word in X,Y by assumption.
 rewrite X,Y;reflexivity.
Qed.
Theorem eckey_tweak_value_matches_add (ng ax ay:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 eckey_tweak_value ng ax ay=
 match @literal_gej_normalize Alg.CoreFunSem
  (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem ng,(ax,ay))) with
 |inl _=>None|inr point=>Some point end.
Proof.
 intro Curve;destruct (secp_affine_literal_represented ax ay Curve) as [p Input].
 pose proof (eckey_tweak_point_group ng ax ay p Curve Input) as Native.
 pose proof (secp_literal_mixed_group_output (GZnZ.one feP) (@literal_generate Alg.CoreFunSem ng) (ax,ay)
  (secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))) p
  (SMain.one_not_zero secp_group_theory) (secp_literal_generate_group ng) Input) as Literal.
 rewrite SMain.add_comm in Literal.
 pose proof (secp_gej_normalize_same_group _ _ _ Native Literal) as Same.
 assert (Left:eckey_tweak_value ng ax ay=match @literal_gej_normalize Alg.CoreFunSem (eckey_tweak_point ng ax ay) with
  |inl _=>None|inr point=>Some point end).
 { rewrite literal_gej_normalize_flag_value;unfold eckey_tweak_value,eckey_tweak_infinite;
   destruct (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (eckey_tweak_point ng ax ay)));reflexivity. }
 rewrite Left,Same;reflexivity.
Qed.
Theorem tweak_bytes_value_matches_add (ng ax ay:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 tweak_bytes_value ng ax ay=
 if tweak_bytes_overflow ng then None else
 match @literal_gej_normalize Alg.CoreFunSem
  (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem ng,(ax,ay))) with
 |inl _=>None|inr point=>Some point end.
Proof.
 intro Curve;unfold tweak_bytes_value;destruct (tweak_bytes_overflow ng);[reflexivity|].
 apply eckey_tweak_value_matches_add;exact Curve.
Qed.

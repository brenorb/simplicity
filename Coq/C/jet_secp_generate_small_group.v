(** Normalize the actual nonzero signed generator digits. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_odd C.jet_secp_curve_group_cyclic
 C.jet_secp_curve_group_scalar_sign C.jet_secp_signed_group_action C.jet_secp_lookup5_group
 C.jet_secp_canonical_scalar C.jet_secp_field_word_group C.jet_secp_jacobian_group
 C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group C.jet_secp_generate_literal
 C.jet_secp_generate_group C.jet_secp_gej_norm_literal C.jet_word_repr.
Require Import C.jet_secp_norm_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_generate_small_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque EGroup.gpow SMain.opp secp_curve_group secp_group_generator
 literal_generate_signed literal_generate_small secp_field_word.
Lemma secp_generator_positive_nonzero k:0<k<canonical_group_order ->
 EGroup.gpow secp_group_generator secp_curve_group k<>secp_group_infinity.
Proof.
 intro Range;apply (EGroup.gpow_support_not_e secp_group_point (SMain.ceqb secp_group_theory)
  secp_group_add secp_group_generator secp_curve_group (secp_group_points_complete secp_group_generator) k).
 change (0<k<Z.of_nat (length secp_generator_powers));rewrite secp_generator_powers_order;exact Range.
Qed.
Lemma secp_generator_signed_nonzero k:0<Z.abs k<canonical_group_order ->
 secp_group_signed_power secp_group_generator k<>secp_group_infinity.
Proof.
 intro Range;unfold secp_group_signed_power;destruct (k <? 0) eqn:Negative.
 - apply Z.ltb_lt in Negative;rewrite Z.abs_neq in Range by lia.
   intro Equal;apply (secp_generator_positive_nonzero (-k) Range).
   pose proof (f_equal (SMain.opp secp_group_theory) Equal) as Back.
   rewrite SMain.opp_opp,secp_group_opp_infinity in Back;exact Back.
 - apply Z.ltb_ge in Negative;rewrite Z.abs_eq in Range by lia.
   apply secp_generator_positive_nonzero;exact Range.
Qed.
Lemma secp_generator_signed_word_bounds n (word:Ty.tySem (Word n)):
 -secp_generator_modulus n<=secp_generator_signed_word n word<secp_generator_modulus n.
Proof.
 pose proof (word_toZ_range n word) as Range.
 unfold secp_generator_signed_word,secp_generator_modulus.
 destruct (@Word.leftmost Bit n Alg.CoreFunSem word) as [u|u];destruct u;
 [change (@toZ BitToZ (inl tt)) with 0|change (@toZ BitToZ (inr tt)) with 1];lia.
Qed.
Local Opaque secp_generator_signed_word.
Lemma secp_generator_base_signed_action (second:bool) (k:Z):
 secp_group_signed_power (EGroup.gpow secp_group_generator secp_curve_group (if second then 2^128 else 1)) k=
 secp_group_signed_power secp_group_generator ((if second then 2^128 else 1)*k).
Proof.
 transitivity (secp_group_signed_power
  (secp_group_signed_power secp_group_generator (if second then 2^128 else 1)) k).
 - apply (f_equal (fun point=>secp_group_signed_power point k)).
   symmetry;apply secp_group_signed_power_nonnegative;destruct second;cbn;lia.
 - apply secp_group_signed_power_multiply.
Qed.
Lemma secp_word_rep_finite_z (c:secp_group_field) (x y z:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_jacobian_word_rep c ((x,y),z) p ->p<>secp_group_infinity ->secp_field_word z<>GZnZ.zero feP.
Proof.
 intros [Curve Value] Finite Zero;cbn [fst snd] in Curve,Value;apply Finite;rewrite <-Value.
 apply (proj2 (secp_jacobian_group_infinity_iff _ _ _ Curve)).
 rewrite Zero;unfold secp_group_field in *;ring.
Qed.
Theorem secp_literal_generate_small_group (second:bool) (word:Ty.tySem (Word 4)):
 secp_generator_signed_word 4 word<>0 ->
 secp_affine_word_rep (GZnZ.one feP) (@literal_generate_small second Alg.CoreFunSem word)
 (secp_group_signed_power secp_group_generator
  ((if second then 2^128 else 1)*secp_generator_signed_word 4 word)).
Proof.
 intro Nonzero.
 pose proof (secp_literal_generate_signed_group 4 second word) as Generated.
 rewrite secp_generator_base_signed_action in Generated.
 pose proof (secp_generator_signed_word_bounds 4 word) as Range.
 change (-65536<=secp_generator_signed_word 4 word<65536) in Range.
 assert (Small:0<Z.abs ((if second then 2^128 else 1)*secp_generator_signed_word 4 word)<canonical_group_order).
 { destruct second;cbn;destruct (Z_le_dec (secp_generator_signed_word 4 word) 0);
   [rewrite Z.abs_neq by nia|rewrite Z.abs_eq by nia|rewrite Z.abs_neq by nia|rewrite Z.abs_eq by nia];
   unfold canonical_group_order;nia. }
 pose proof (secp_generator_signed_nonzero _ Small) as Finite.
 Local Transparent literal_generate_small.
 change (secp_affine_word_rep (GZnZ.one feP)
  (@literal_gej_norm Alg.CoreFunSem
   (@literal_generate_signed 4 Alg.CoreFunSem (@literal_generator_base second Alg.CoreFunSem) word))
  (secp_group_signed_power secp_group_generator
   ((if second then 2^128 else 1)*secp_generator_signed_word 4 word))).
 destruct (@literal_generate_signed 4 Alg.CoreFunSem (@literal_generator_base second Alg.CoreFunSem) word)
  as [[x y] z].
 apply secp_literal_gej_norm_group;[eapply secp_word_rep_finite_z;eassumption|exact Generated].
Qed.
Require Import C.jet_secp_wnaf_literal_values C.jet_secp_wnaf_literal_mask.
Local Transparent secp_generator_signed_word.
Lemma secp_generator_signed_word16 (word:Ty.tySem (Word 4)):
 secp_generator_signed_word 4 word=literal_wnaf_signed16 word.
Proof. reflexivity. Qed.
Local Opaque secp_generator_signed_word.
Theorem secp_literal_generate_small_valid_group (second:bool) (word:Ty.tySem (Word 4)):
 wnaf_literal_valid (inr word) ->
 secp_affine_word_rep (GZnZ.one feP) (@literal_generate_small second Alg.CoreFunSem word)
 (secp_group_signed_power secp_group_generator ((if second then 2^128 else 1)*literal_wnaf_signed16 word)).
Proof.
 intros [Odd Bounds];rewrite <-secp_generator_signed_word16.
 apply secp_literal_generate_small_group;intro Zero.
 rewrite secp_generator_signed_word16 in Zero;rewrite Zero in Odd;discriminate.
Qed.

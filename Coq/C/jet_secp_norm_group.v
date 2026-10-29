(** Reuse the checked literal EEA inverse when normalizing represented points. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_field_word_group C.jet_secp_jacobian_word_group C.jet_secp_jacobian_word_transforms
 C.jet_secp_table_pass2_group C.jet_secp_invert_literal C.jet_secp_invert_modinv C.jet_predicate_spec
 C.jet_secp_gej_norm_literal C.jet_secp_rescale_literal C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_norm_group_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque literal_fe_invert literal_gej_norm literal_gej_zinv.
Lemma secp_field_word_invert_product (z:Ty.tySem (Word 8)):
 secp_field_word z<>GZnZ.zero feP ->
 GZnZ.mul feP (secp_field_word z) (secp_field_word (@literal_fe_invert Alg.CoreFunSem z))=GZnZ.one feP.
Proof.
 intro Nonzero;pose proof (word_value_bounds 8 z) as Range.
 change (0<=@toZ (WordToZ 8) z<2^256) in Range.
 assert (NonzeroInteger:@toZ (WordToZ 8) z<>0).
 { intro Zero;apply Nonzero;unfold secp_field_word;rewrite Zero.
   apply GZnZ.zirr;reflexivity. }
 assert (Nonmultiple:@toZ (WordToZ 8) z<>feP).
 { intro Equal;apply Nonzero;unfold secp_field_word;rewrite Equal;apply secp_field_integer_p. }
 destruct (literal_invert_numeric_inverse (@toZ (WordToZ 8) z) ltac:(lia) Nonmultiple) as [_ Product].
 unfold secp_field_word;rewrite literal_fe_invert_numeric,<-secp_field_integer_mul.
 apply GZnZ.zirr.
 change ((@toZ (WordToZ 8) z*literal_invert_numeric (@toZ (WordToZ 8) z)) mod feP=1).
 rewrite Z.mul_comm;exact Product.
Qed.
Local Opaque secp_field_word.
Lemma secp_field_word_inverse_nonzero (z:Ty.tySem (Word 8)):
 secp_field_word z<>GZnZ.zero feP ->
 secp_field_word (@literal_fe_invert Alg.CoreFunSem z)<>GZnZ.zero feP.
Proof.
 intro Nonzero;pose proof (secp_field_word_invert_product z Nonzero) as Product.
 intro Zero;apply (SMain.one_not_zero secp_group_theory).
 rewrite <-Product,Zero;unfold secp_group_field in *;ring.
Qed.
Theorem secp_literal_gej_norm_group (x y z:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_field_word z<>GZnZ.zero feP ->secp_jacobian_word_rep (GZnZ.one feP) ((x,y),z) p ->
 secp_affine_word_rep (GZnZ.one feP) (@literal_gej_norm Alg.CoreFunSem ((x,y),z)) p.
Proof.
 intros Nonzero Represented.
 pose proof (secp_literal_zinv_context_group (GZnZ.one feP) x y z
  (@literal_fe_invert Alg.CoreFunSem z) p (secp_field_word_inverse_nonzero z Nonzero) Represented) as Normalized.
 assert (Unit:GZnZ.mul feP (GZnZ.mul feP (GZnZ.one feP) (secp_field_word z))
  (secp_field_word (@literal_fe_invert Alg.CoreFunSem z))=GZnZ.one feP).
 { pose proof (secp_field_word_invert_product z Nonzero) as Product.
   unfold secp_group_field in *;ring [Product]. }
 rewrite Unit in Normalized;exact Normalized.
Qed.

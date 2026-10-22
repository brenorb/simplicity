(** Dispatch correspondence after the actual point-negation and weak-normalizer.
    These residue lemmas preserve arbitrary Word256 inputs, including off-curve
    and noncanonical coordinates; no field primality premise is needed here. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_field_negate_separate C.jet_secp_field_weak_loose C.jet_secp_field_weak_tight
 C.jet_secp_multiply_input_input C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal
 C.jet_secp_double_coordinate_numeric C.jet_secp_mixed_dispatch_literal
 C.jet_secp_mixed_finite_return C.jet_secp_mixed_finite_prefix C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
 C.jet_secp_curve_literal C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_reader_rho negate_sep_words weak_loose_words
 canonical_fe_normalize canonical_fe_is_zero literal_fe_negate normalized_value.

Lemma equiv_normalized_reader_residue (a : Ty.tySem (Word 8)) :
 radix_value (square_reader_rho a) mod feP=
 @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a) mod feP.
Proof.
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model,
  Z.mod_mod by (unfold feP,feR;lia).
 rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Lemma equiv_negated_reader_residue (a : Ty.tySem (Word 8)) :
 radix_value (negate_sep_words (square_reader_rho a)) mod feP=
 @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem a).
Proof.
 apply double_negate_sep_matches.
 - apply mixed_positioned_tight;apply square_reader_positioned.
 - rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Lemma equiv_weak_negated_reader (a : Ty.tySem (Word 8)) :
 radix_value (weak_loose_words (negate_sep_words (square_reader_rho a))) mod feP=
 @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem a) mod feP /\
 mul_small_input_bounds (weak_loose_words (negate_sep_words (square_reader_rho a))).
Proof.
 assert (Bound : forall i,(i<5)%nat ->
   Int64.unsigned (negate_sep_words (square_reader_rho a) i)<=2^60).
 { exact (negate_reader_loose_bound (normalized_value a) (normalized_value_range a)). }
 destruct (weak_loose_numeric _ Bound) as [Residue Bounds];split;[|exact Bounds].
 rewrite Residue;apply double_match_mod;apply equiv_negated_reader_residue.
Qed.

Lemma mixed_h_residue_test x z u (a c b : Ty.tySem (Word 8)) :
 mul_small_input_bounds x -> square_input_bounds z -> square_input_bounds u ->
 radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) b mod feP ->
 Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h a c b)).
Proof.
 intros BX BZ BU HX HZ HU.
 rewrite (mixed_h_residue x z u _ _ _ BX BZ BU HX HZ HU),
  literal_curve_zero_numeric,mixed_literal_h_numeric,Z.mod_mod by (unfold feP,feR;lia).
 replace (@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c-@toZ (WordToZ 8) a) with
  (-(@toZ (WordToZ 8) a-@toZ (WordToZ 8) b*@toZ (WordToZ 8) c*@toZ (WordToZ 8) c)) by ring.
 apply mixed_negated_zero_test.
Qed.

Lemma mixed_i_residue_test y z v (a c b : Ty.tySem (Word 8)) :
 mul_small_input_bounds y -> square_input_bounds z -> square_input_bounds v ->
 radix_value y mod feP=@toZ (WordToZ 8) a mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) b mod feP ->
 Z.eqb (radix_value (mixed_i_words y z v) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i a c b)).
Proof.
 intros BY BZ BV HY HZ HV.
 rewrite (mixed_i_residue y z v _ _ _ BY BZ BV HY HZ HV),
  literal_curve_zero_numeric,mixed_literal_i_numeric,Z.mod_mod by (unfold feP,feR;lia).
 reflexivity.
Qed.

Lemma equiv_negated_h_test (x z u : Ty.tySem (Word 8)) :
 Z.eqb (radix_value (mixed_h_words (square_reader_rho x) (square_reader_rho z)
  (square_reader_rho u)) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
  (mixed_literal_h (@canonical_fe_normalize Alg.CoreFunSem x)
   (@canonical_fe_normalize Alg.CoreFunSem z) u)).
Proof.
 apply mixed_h_residue_test;try apply square_reader_bounds;
  try (apply mixed_positioned_tight;apply square_reader_positioned);
  try apply equiv_normalized_reader_residue.
 rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Lemma equiv_negated_i_test (y z v : Ty.tySem (Word 8)) :
 Z.eqb (radix_value (mixed_i_words (weak_loose_words (negate_sep_words (square_reader_rho y)))
  (square_reader_rho z) (square_reader_rho v)) mod feP) 0=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
  (mixed_literal_i (@literal_fe_negate Alg.CoreFunSem y)
   (@canonical_fe_normalize Alg.CoreFunSem z) v)).
Proof.
 apply mixed_i_residue_test.
 - exact (proj2 (equiv_weak_negated_reader y)).
 - apply square_reader_bounds.
 - apply square_reader_bounds.
 - exact (proj1 (equiv_weak_negated_reader y)).
 - apply equiv_normalized_reader_residue.
 - rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

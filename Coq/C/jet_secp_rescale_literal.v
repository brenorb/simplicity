(** Literal LibSecp256k1 gej_rescale/zinv trees and the residue bridge for
    the actual helper outputs.  No curve or nonzero-scale premise is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_multiply_finish_product C.jet_secp_negate_literal_contract C.jet_secp_multiply_literal_spec.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_numeric.
Require Import C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric.
Require Import C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_canonical_normalize C.jet_secp_multiply_input_input C.jet_secp_square_spec_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

(** Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:746,763,552.
    Keep the cube and zinv structure, not an algebraically rewritten target. *)
Definition literal_fe_cube {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  iden &&& @literal_fe_square term >>> @literal_fe_multiply term.
Definition literal_gej_zinv {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8)) :=
  (O (O H) &&& I (@literal_fe_square term) >>> @literal_fe_multiply term) &&&
  (O (I H) &&& I (@literal_fe_cube term) >>> @literal_fe_multiply term).
Definition literal_gej_rescale {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Word 8))
    (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) :=
  (O (O H) &&& I H >>> @literal_gej_zinv term) &&&
  (O (I H) &&& I H >>> @literal_fe_multiply term).

Local Opaque literal_fe_multiply literal_fe_square point_mul_words square_words.
Lemma literal_gej_rescale_step (x y z s : tySem (Word 8)) :
  @literal_gej_rescale Alg.CoreFunSem (((x,y),z),s) =
    ((@literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem s),
      @literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_cube Alg.CoreFunSem s)),
      @literal_fe_multiply Alg.CoreFunSem (z,s)).
Proof. reflexivity. Qed.

Lemma rescale_multiply_associates (y s : tySem (Word 8)) :
  @literal_fe_multiply Alg.CoreFunSem
    (@literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_square Alg.CoreFunSem s),s) =
  @literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_cube Alg.CoreFunSem s).
Proof.
  apply (toZ_injective (WordToZ 8)).
  change (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
      (@literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_square Alg.CoreFunSem s),s)) =
    @toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem
      (y,@literal_fe_multiply Alg.CoreFunSem (s,@literal_fe_square Alg.CoreFunSem s)))).
  rewrite !literal_multiply_numeric.
  rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by (unfold feP, feR; discriminate).
  f_equal; ring.
Qed.

Lemma rescale_reader_residue (x : tySem (Word 8)) :
  radix_value (square_reader_rho x) mod field_prime = @toZ (WordToZ 8) x mod field_prime.
Proof.
  unfold square_reader_rho; rewrite radix_limb_rho by apply normalized_value_range.
  unfold normalized_value; rewrite canonical_fe_normalize_numeric, canonical_field_order_matches_limb_model.
  change ((@toZ (WordToZ 8) x mod field_prime) mod field_prime =
    @toZ (WordToZ 8) x mod field_prime).
  apply Z.mod_mod; unfold field_prime, field_c; discriminate.
Qed.

Definition rescale_field_output (w : nat -> int64) :=
  wide_fe_output (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat).
Lemma rescale_writer_bounds w : square_input_bounds w ->
  forall i, (i < 5)%nat -> Int64.unsigned (w i) <= 2^60.
Proof.
  intros HB i HI; pose proof (HB i HI); destruct (Nat.eqb i 4); lia.
Qed.
Lemma rescale_field_output_value w :
  @toZ (WordToZ 8) (rescale_field_output w) = radix_value w mod field_prime.
Proof.
  unfold rescale_field_output.
  rewrite wide_fe_output_value, radix_value_as_fe_val; reflexivity.
Qed.

Lemma rescale_mul_writer a b (x y : tySem (Word 8)) :
  square_input_bounds a -> square_input_bounds b ->
  radix_value a mod field_prime = @toZ (WordToZ 8) x mod field_prime ->
  radix_value b mod field_prime = @toZ (WordToZ 8) y mod field_prime ->
  rescale_field_output (point_mul_words a b) =
    @literal_fe_multiply Alg.CoreFunSem (x,y).
Proof.
  intros BA BB HA HB; apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value, (proj1 (point_mul_value_and_bounds a b BA BB)), literal_multiply_numeric.
  change ((radix_value a * radix_value b) mod field_prime =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) y) mod field_prime).
  rewrite (Z.mul_mod (radix_value a) (radix_value b)), HA, HB, <- Z.mul_mod by
    (unfold field_prime, field_c; discriminate).
  reflexivity.
Qed.

Lemma rescale_square_writer a (x : tySem (Word 8)) : square_input_bounds a ->
  radix_value a mod field_prime = @toZ (WordToZ 8) x mod field_prime ->
  rescale_field_output (square_words a) = @literal_fe_square Alg.CoreFunSem x.
Proof.
  intros BA HA; apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value, square_output_numeric by exact BA.
  rewrite literal_square_numeric.
  change ((radix_value a * radix_value a) mod field_prime =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod field_prime).
  rewrite (Z.mul_mod (radix_value a) (radix_value a)), HA, <- Z.mul_mod by
    (unfold field_prime, field_c; discriminate).
  reflexivity.
Qed.

Theorem rescale_helper_outputs_literal a b c d (x y z s : tySem (Word 8)) :
  square_input_bounds a -> square_input_bounds b -> square_input_bounds c -> square_input_bounds d ->
  radix_value a mod field_prime = @toZ (WordToZ 8) x mod field_prime ->
  radix_value b mod field_prime = @toZ (WordToZ 8) y mod field_prime ->
  radix_value c mod field_prime = @toZ (WordToZ 8) z mod field_prime ->
  radix_value d mod field_prime = @toZ (WordToZ 8) s mod field_prime ->
  ((rescale_field_output (point_mul_words a (square_words d)),
     rescale_field_output (point_mul_words (point_mul_words b (square_words d)) d)),
    rescale_field_output (point_mul_words c d)) =
    @literal_gej_rescale Alg.CoreFunSem (((x,y),z),s).
Proof.
  intros BA BB BC BD HA HB HC HD.
  assert (BSD : square_input_bounds (square_words d)).
  { intros i HI; pose proof (square_output_bounds d BD i HI); destruct (Nat.eqb i 4); lia. }
  pose proof (rescale_square_writer d s BD HD) as HS.
  assert (HSD : radix_value (square_words d) mod field_prime =
      @toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem s) mod field_prime).
  { rewrite <- HS, rescale_field_output_value, Z.mod_mod by (unfold field_prime, field_c; discriminate).
    reflexivity. }
  pose proof (rescale_mul_writer a (square_words d) x (@literal_fe_square Alg.CoreFunSem s) BA BSD HA HSD) as HX.
  pose proof (rescale_mul_writer b (square_words d) y (@literal_fe_square Alg.CoreFunSem s) BB BSD HB HSD) as HY.
  assert (HBY : square_input_bounds (point_mul_words b (square_words d))) by
    (exact (proj2 (point_mul_value_and_bounds b (square_words d) BB BSD))).
  assert (HYV : radix_value (point_mul_words b (square_words d)) mod field_prime =
    @toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (y,@literal_fe_square Alg.CoreFunSem s)) mod field_prime).
  { rewrite <- HY, rescale_field_output_value, Z.mod_mod by (unfold field_prime, field_c; discriminate).
    reflexivity. }
  rewrite HX, (rescale_mul_writer _ d _ s HBY BD HYV HD), (rescale_mul_writer c d z s BC BD HC HD).
  rewrite rescale_multiply_associates, literal_gej_rescale_step; reflexivity.
Qed.

Theorem rescale_reader_outputs_literal (x y z s : tySem (Word 8)) :
  ((rescale_field_output (point_mul_words (square_reader_rho x) (square_words (square_reader_rho s))),
    rescale_field_output (point_mul_words
      (point_mul_words (square_reader_rho y) (square_words (square_reader_rho s))) (square_reader_rho s))),
    rescale_field_output (point_mul_words (square_reader_rho z) (square_reader_rho s))) =
  @literal_gej_rescale Alg.CoreFunSem (((x,y),z),s).
Proof.
  apply rescale_helper_outputs_literal; first [apply square_reader_bounds | apply rescale_reader_residue].
Qed.

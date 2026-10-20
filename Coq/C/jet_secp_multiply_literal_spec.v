(** Connect the actual C numeric result to the existing literal Simplicity term. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_multiply_spec.
Require Import C.jet_secp_fe_math C.jet_secp_write_fe_numeric C.jet_secp_canonical_normalize.
Require Import C.jet_secp_canonical_negate C.jet_secp_negate_literal_contract.
(** The source-correspondence foundation's formal conversion theorem is also
    loaded and recursively checked, not merely scanned as source. *)
Require C.jet_haskell_word_conversion.
Require Import C.jet_secp_multiply_input_input.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_multiply canonical_fe_normalize512 multiply_word_spec.

Lemma literal_multiply_numeric (x y : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (x, y)) =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) y) mod feP.
Proof.
  rewrite literal_fe_multiply_matches; unfold canonical_fe_multiply.
  change (@toZ (WordToZ 8)
    (@canonical_fe_normalize512 Alg.CoreFunSem (@multiply_word_spec 8 Alg.CoreFunSem (x, y))) =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) y) mod feP).
  rewrite canonical_fe_normalize512_numeric, multiply_word_spec_numeric,
    canonical_field_order_matches_limb_model; reflexivity.
Qed.

Lemma input_product_matches_literal (x y : Ty.tySem (Word 8)) :
  input_product_word x y = @literal_fe_multiply Alg.CoreFunSem (x, y).
Proof.
  apply (toZ_injective (WordToZ 8)); rewrite literal_multiply_numeric.
  unfold input_product_word; rewrite to_fromZ; apply Z.mod_small.
  change (0 <= (@toZ (WordToZ 8) x * @toZ (WordToZ 8) y) mod feP < 2 ^ 256).
  apply field_mod_256_range.
Qed.

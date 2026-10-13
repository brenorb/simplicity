(** Numeric bridges for comparison with actual C limbs; the canonical
    specification remains the literal Core program in the imported port. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_predicate_spec C.jet_canonical_add_adapter.
Require Import C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric.
Require Import C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_negate.
Require Import C.jet_secp_canonical_scalar_add.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma canonical_scalar_add_numeric (a b : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@canonical_scalar_add Alg.CoreFunSem (a,b)) =
  (@toZ (WordToZ 8) a + @toZ (WordToZ 8) b) mod canonical_group_order.
Proof.
  change (@toZ (WordToZ 8)
    (@canonical_scalar_normalize512 Alg.CoreFunSem
      (@literal_fe_add_expand Alg.CoreFunSem
        (@canonical_add_word 8 Alg.CoreFunSem (a,b)))) =
    (@toZ (WordToZ 8) a + @toZ (WordToZ 8) b) mod canonical_group_order).
  rewrite canonical_scalar_normalize512_numeric, literal_fe_add_expand_pair_value,
    canonical_add_word_matches_adder, Word.adder_correct; reflexivity.
Qed.

Lemma canonical_scalar_add_normalize_value (a b : Ty.tySem (Word 8)) :
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a) +
   @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b)) mod canonical_group_order =
  @toZ (WordToZ 8) (@canonical_scalar_add Alg.CoreFunSem (a,b)).
Proof.
  rewrite !canonical_scalar_normalize_numeric, canonical_scalar_add_numeric.
  symmetry; apply Z.add_mod.
  pose proof canonical_group_order_range; lia.
Qed.

Lemma canonical_scalar_add_normalized_inputs_range (a b : Ty.tySem (Word 8)) :
  0 <= @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a) +
       @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b)
    < 2 * canonical_group_order.
Proof.
  rewrite !canonical_scalar_normalize_numeric.
  assert (HN : 0 < canonical_group_order) by (pose proof canonical_group_order_range; lia).
  pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) a) canonical_group_order HN).
  pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) b) canonical_group_order HN); lia.
Qed.

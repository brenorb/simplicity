(** Preserve the full Word256 domain across the real reader's normalization. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_secp_canonical_normalize C.jet_secp_canonical_negate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_negate.

Lemma canonical_normalized_field_range (x : Ty.tySem (Word 8)) :
  0 <= @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x) < canonical_field_order.
Proof.
  rewrite canonical_fe_normalize_numeric. apply Z.mod_pos_bound.
  pose proof canonical_field_order_range; lia.
Qed.

Lemma canonical_fe_negate_normalized_input (x : Ty.tySem (Word 8)) :
  @canonical_fe_negate Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem x) =
  @canonical_fe_negate Alg.CoreFunSem x.
Proof.
  apply (toZ_injective (WordToZ 8)).
  rewrite !canonical_fe_negate_numeric, canonical_fe_normalize_numeric.
  set (v := @toZ (WordToZ 8) x).
  rewrite (Zminus_mod canonical_field_order (v mod canonical_field_order) canonical_field_order),
    (Zminus_mod canonical_field_order v canonical_field_order).
  rewrite Z.mod_mod by (pose proof canonical_field_order_range; lia).
  reflexivity.
Qed.
Print Assumptions canonical_fe_negate_normalized_input.

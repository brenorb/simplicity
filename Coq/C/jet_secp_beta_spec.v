(** Literal pinned fe_beta and fe_multiply_beta wiring. The specification's
    (beta,x) order is retained, although the C helper takes (x,beta). *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_word_repr C.jet_predicate_spec C.jet_secp_fe_math C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_canonical_normalize C.jet_secp_negate_literal_contract.
Require Import C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_writer_bridge C.jet_secp_multiply_input_input C.jet_secp_multiply_literal_spec.
Require Import C.jet_secp_beta_global C.jet_secp_beta_inputs.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition beta_word : Ty.tySem (Word 8) := @fromZ (WordToZ 8) beta_value.
Definition literal_fe_beta {term : Alg.Core.Algebra} : term Ty.Unit (Word 8) := Alg.scribe beta_word.
Definition literal_fe_multiply_beta {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  (unit >>> @literal_fe_beta term) &&& iden >>> @literal_fe_multiply term.

Lemma beta_value_range : 0 <= beta_value < feP /\ beta_value < word_modulus 8.
Proof. vm_compute; intuition discriminate. Qed.
Lemma beta_word_value : @toZ (WordToZ 8) beta_word = beta_value.
Proof.
  unfold beta_word; rewrite to_fromZ; apply Z.mod_small.
  change (0 <= beta_value < word_modulus 8); pose proof beta_value_range; lia.
Qed.
Local Opaque literal_fe_multiply beta_word.
Lemma beta_literal_step x : @literal_fe_multiply_beta Alg.CoreFunSem x =
  @literal_fe_multiply Alg.CoreFunSem (beta_word, x).
Proof.
  unfold literal_fe_multiply_beta, literal_fe_beta.
  change (@literal_fe_multiply Alg.CoreFunSem (@Alg.scribe Ty.Unit (Word 8) beta_word Alg.CoreFunSem tt, x) =
    @literal_fe_multiply Alg.CoreFunSem (beta_word, x)).
  rewrite Alg.scribe_correct; reflexivity.
Qed.
Lemma beta_literal_numeric x : @toZ (WordToZ 8) (@literal_fe_multiply_beta Alg.CoreFunSem x) =
  (beta_value * @toZ (WordToZ 8) x) mod feP.
Proof. rewrite beta_literal_step, literal_multiply_numeric, beta_word_value; reflexivity. Qed.

Lemma beta_product_matches_literal x : product_word (beta_input_rho x) =
  @literal_fe_multiply_beta Alg.CoreFunSem x.
Proof.
  apply (toZ_injective (WordToZ 8)); rewrite beta_literal_numeric.
  unfold product_word; rewrite beta_input_left_value, beta_input_right_value,
    field_prime_matches_normalizer, to_fromZ.
  rewrite Z.mod_small by (change (0 <= (normalized_value x * beta_value) mod feP < 2^256); apply field_mod_256_range).
  unfold normalized_value; rewrite canonical_fe_normalize_numeric, canonical_field_order_matches_limb_model.
  rewrite Z.mul_mod_idemp_l by (unfold feP, feR; discriminate).
  rewrite Z.mul_comm; reflexivity.
Qed.

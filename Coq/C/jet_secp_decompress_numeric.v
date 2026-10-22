(** Match the actual cubic-plus-seven root input to the canonical expression.
    These are representation bridges used by the C execution proof. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_separate_numeric C.jet_secp_square_execution C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_field_mul_small C.jet_secp_field_add7 C.jet_secp_double_coordinate_numeric
 C.jet_secp_curve_literal C.jet_secp_rescale_literal C.jet_secp_literal_add_program
 C.jet_secp_literal_add_numeric C.jet_secp_canonical_normalize C.jet_secp_root_chain_numeric
 C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words point_mul_words literal_fe_cube literal_fe_add.

Definition decompress_cubic_words w := point_mul_words w (square_words w).
Definition decompress_root_words w := add7_words (decompress_cubic_words w).
Definition decompress_root_input (x : Ty.tySem (Word 8)) :=
 @literal_fe_add Alg.CoreFunSem (curve_seven_word,@literal_fe_cube Alg.CoreFunSem x).

Lemma add7_tight_no_wrap w : mul_small_input_bounds w ->
 Int64.unsigned (w 0%nat)+7<=Int64.max_unsigned.
Proof.
 intro B;pose proof (B 0%nat ltac:(lia)) as B0;cbn [Nat.eqb] in B0.
 change Int64.max_unsigned with 18446744073709551615;lia.
Qed.
Lemma add7_tight_square_bounds w : mul_small_input_bounds w -> square_input_bounds (add7_words w).
Proof.
 intros B i HI;unfold add7_words;destruct (Nat.eqb i 0) eqn:Zero.
 - apply Nat.eqb_eq in Zero;subst i;cbn [Nat.eqb].
   unfold Int64.add;change (Int64.unsigned (Int64.repr 7)) with 7.
   rewrite Int64.unsigned_repr by (pose proof (Int64.unsigned_range (w 0%nat));pose proof (add7_tight_no_wrap w B);lia).
   pose proof (B 0%nat ltac:(lia)) as B0;cbn [Nat.eqb] in B0;lia.
 - pose proof (B i HI);destruct (Nat.eqb i 4);lia.
Qed.
Lemma decompress_cubic_tight w : square_input_bounds w -> mul_small_input_bounds (decompress_cubic_words w).
Proof. intro B;apply double_mul_tight;[exact B|apply square_result_reusable;exact B]. Qed.
Local Transparent literal_fe_cube.
Lemma decompress_literal_cube_step (x : Ty.tySem (Word 8)) :
 @literal_fe_cube Alg.CoreFunSem x=@literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem x).
Proof. unfold literal_fe_cube;reflexivity. Qed.
Local Opaque literal_fe_cube.
Lemma decompress_cubic_matches w x : root_words_match w x ->
 radix_value (decompress_cubic_words w) mod feP=@toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem x).
Proof.
 intros [B R];unfold decompress_cubic_words.
 rewrite decompress_literal_cube_step.
 apply double_mul_matches;[exact B|apply square_result_reusable;exact B|exact R|].
 apply double_match_mod;apply double_square_matches;assumption.
Qed.
Lemma decompress_root_matches w x : root_words_match w x ->
 root_words_match (decompress_root_words w) (decompress_root_input x).
Proof.
 intro Match;pose proof (decompress_cubic_tight w (proj1 Match)) as Tight.
 split;[apply add7_tight_square_bounds;exact Tight|].
 unfold decompress_root_words,decompress_root_input.
 rewrite add7_radix by (apply add7_tight_no_wrap;exact Tight).
 apply double_match_mod;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,curve_seven_value.
 rewrite Z.add_comm;apply double_residue_sum;[reflexivity|apply double_match_mod;apply decompress_cubic_matches;exact Match].
Qed.

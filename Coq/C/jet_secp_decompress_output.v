(** Serialization bridge from the actual retained/negated C limbs to the
    fixed canonical decompression expression. No curve-input restriction. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_write_fe_wide_values
 C.jet_secp_rescale_literal C.jet_secp_point_write_field C.jet_secp_point_field_bridge
 C.jet_secp_canonical_normalize C.jet_secp_canonical_odd C.jet_secp_canonical_negate
 C.jet_secp_negate_literal_contract C.jet_secp_field_negate_storage C.jet_secp_write_fe_numeric
 C.jet_secp_root_chain_numeric C.jet_secp_root_check C.jet_secp_root_literal C.jet_secp_root_function_literal
 C.jet_secp_decompress_numeric C.jet_secp_decompress_literal C.jet_secp_decompress_parity
 C.jet_secp_decompress_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque root_check_flag root_chain_candidate decompress_root_words rescale_field_output
 literal_fe_square_root literal_root_candidate literal_y_from_x literal_decompress
 canonical_fe_normalize canonical_fe_is_odd canonical_fe_negate literal_fe_negate.

Definition decompress_input_field (w : nat -> int64) := mkpointfield (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat).
Definition decompress_parity_field value (odd : bool) := if xorb (Z.testbit value 0) odd
 then point_negative_field value else point_canonical_field value.
Definition decompress_y_field w odd := if root_check_flag (decompress_root_words w)
 then decompress_parity_field (decompress_body_value w) odd
 else decompress_input_field (root_chain_candidate (decompress_root_words w)).
Definition decompress_machine_result w (odd : bool) : Ty.tySem (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 8))) :=
 if root_check_flag (decompress_root_words w)
 then inr (point_field_output (decompress_input_field w),point_field_output (decompress_y_field w odd)) else inl tt.

Lemma decompress_input_limbs w : point_field_limbs (decompress_input_field w)=words5 w.
Proof. reflexivity. Qed.
Lemma decompress_parity_field_limbs value odd :
 point_field_limbs (decompress_parity_field value odd)=decompress_parity_limbs value odd.
Proof.
 unfold decompress_parity_field,decompress_parity_limbs;destruct (xorb (Z.testbit value 0) odd);
  [apply point_negative_field_limbs|apply point_canonical_field_limbs].
Qed.
Lemma decompress_y_field_limbs w odd : point_field_limbs (decompress_y_field w odd)=decompress_body_y w odd.
Proof.
 unfold decompress_y_field,decompress_body_y;destruct (root_check_flag (decompress_root_words w));
  [apply decompress_parity_field_limbs|apply decompress_input_limbs].
Qed.
Lemma decompress_input_field_output w : point_field_output (decompress_input_field w)=rescale_field_output w.
Proof. reflexivity. Qed.
Lemma decompress_normalize_fixed (y : Ty.tySem (Word 8)) : @toZ (WordToZ 8) y<feP ->
 @canonical_fe_normalize Alg.CoreFunSem y=y.
Proof.
 intro Bound;apply (toZ_injective (WordToZ 8));rewrite canonical_fe_normalize_numeric,
  canonical_field_order_matches_limb_model;apply Z.mod_small;pose proof (word_toZ_range 8 y);lia.
Qed.
Lemma decompress_parity_field_output (y : Ty.tySem (Word 8)) (odd : bool) : @toZ (WordToZ 8) y<feP ->
 point_field_output (decompress_parity_field (@toZ (WordToZ 8) y) odd)=
 if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) odd
 then @literal_fe_negate Alg.CoreFunSem y else y.
Proof.
 intro Bound.
 assert (Parity : Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)=Z.testbit (@toZ (WordToZ 8) y) 0).
 { rewrite canonical_fe_is_odd_numeric,(decompress_normalize_fixed y Bound);reflexivity. }
 rewrite Parity;unfold decompress_parity_field;destruct (xorb (Z.testbit (@toZ (WordToZ 8) y) 0) odd).
 - rewrite point_negative_field_output by exact Bound;rewrite literal_fe_negate_matches;reflexivity.
 - rewrite point_canonical_field_output;apply decompress_normalize_fixed;exact Bound.
Qed.
Lemma decompress_input_matches w x : root_words_match w x ->
 point_field_output (decompress_input_field w)=@canonical_fe_normalize Alg.CoreFunSem x.
Proof.
 intros [_ Value];rewrite decompress_input_field_output;apply (toZ_injective (WordToZ 8)).
 rewrite rescale_field_output_value,field_prime_matches_normalizer,canonical_fe_normalize_numeric,
  canonical_field_order_matches_limb_model;exact Value.
Qed.
Lemma decompress_y_from_x_result w x : root_words_match w x ->
 @literal_y_from_x Alg.CoreFunSem x=if root_check_flag (decompress_root_words w)
 then inr (rescale_field_output (root_chain_candidate (decompress_root_words w))) else inl tt.
Proof.
 intro Match;pose proof (decompress_root_matches w x Match) as RootMatch.
 pose proof (root_result_matches _ _ RootMatch) as Result.
 rewrite <-(root_candidate_output _ _ RootMatch) in Result.
 transitivity (@literal_fe_square_root Alg.CoreFunSem (decompress_root_input x));
  [exact (literal_y_from_x_step x)|exact Result].
Qed.
Lemma decompress_candidate_value w :
 @toZ (WordToZ 8) (rescale_field_output (root_chain_candidate (decompress_root_words w)))=decompress_body_value w.
Proof. rewrite rescale_field_output_value,field_prime_matches_normalizer;reflexivity. Qed.
Theorem decompress_machine_matches_literal w x (odd : Ty.tySem Bit) : root_words_match w x ->
 decompress_machine_result w (Bit.toBool odd)=@literal_decompress Alg.CoreFunSem (odd,x).
Proof.
 intro Match;rewrite literal_decompress_step,(decompress_y_from_x_result w x Match).
 unfold decompress_machine_result;destruct (root_check_flag (decompress_root_words w)) eqn:Flag;[|reflexivity].
 cbn [fst snd];rewrite (decompress_input_matches w x Match).
 unfold decompress_y_field;rewrite Flag;rewrite <-decompress_candidate_value.
 rewrite decompress_parity_field_output.
 - reflexivity.
 - rewrite rescale_field_output_value,field_prime_matches_normalizer.
   pose proof (Z.mod_pos_bound (radix_value (root_chain_candidate (decompress_root_words w))) feP
    ltac:(unfold feP,feR;lia));lia.
Qed.

Lemma decompress_input_field_bounded w : square_input_bounds w -> point_field_bounds (decompress_input_field w).
Proof.
 intro Bounds;unfold point_field_bounds,decompress_input_field;cbn [pf0 pf1 pf2 pf3 pf4].
 repeat split;apply (rescale_writer_bounds w Bounds);lia.
Qed.
Lemma decompress_y_field_bounded w x odd : root_words_match w x -> point_field_bounds (decompress_y_field w odd).
Proof.
 intro Match;unfold decompress_y_field;destruct (root_check_flag (decompress_root_words w)).
 - unfold decompress_parity_field;destruct (xorb (Z.testbit (decompress_body_value w) 0) odd).
   + apply point_negative_field_bounded;unfold decompress_body_value;apply field_mod_256_range.
   + apply point_canonical_field_bounded;unfold decompress_body_value;apply field_mod_256_range.
 - apply decompress_input_field_bounded.
   exact (proj1 (root_chain_candidate_matches _ _ (decompress_root_matches w x Match))).
Qed.
Lemma decompress_return_matches_literal w x (odd : Ty.tySem Bit) : root_words_match w x ->
 decompress_body_return w=match @literal_decompress Alg.CoreFunSem (odd,x) with inl _=>Int.zero | inr _=>Int.one end.
Proof.
 intro Match;rewrite <-(decompress_machine_matches_literal w x odd Match).
 unfold decompress_body_return,decompress_machine_result;destruct (root_check_flag (decompress_root_words w));reflexivity.
Qed.

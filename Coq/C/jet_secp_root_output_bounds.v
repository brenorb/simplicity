(** Bounds needed by SWU's final magnitude-one negation. They follow from
    the final original square in the checked root chain, not an assumption
    that the root's noncanonical C limbs are normalized. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_root_chain_numeric C.jet_secp_root_square_loop C.jet_secp_root_literal C.jet_secp_square_execution
  C.jet_secp_field_pair_multiply C.jet_secp_square_numeric C.jet_secp_square_columns
  C.jet_secp_field_mul_small C.jet_secp_multiply_literal_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma root_chain_candidate_tight w (x:Ty.tySem (Word 8)) : root_words_match w x ->
  mul_small_input_bounds (root_chain_candidate w).
Proof.
  intro Match;destruct (root_chain_window_matches w x Match) as [H2 HT].
  pose proof (root_square_match _ _ HT) as H6.
  change (root_words_match (root_square_words 6 (snd (root_chain_window w)))
    (@literal_fe_square Alg.CoreFunSem (snd (@literal_fe_tower Alg.CoreFunSem x)))) in H6.
  pose proof (root_pair_match _ _ _ _ H6 H2) as Product.
  pose proof (root_square_match _ _ Product) as Inner.
  unfold root_chain_candidate;intros i Index.
  exact (proj2 (square_output_bounds _ (proj1 Inner) i Index)).
Qed.

(** Value bridge for the original square-root helper's addition chain.
    Word functions are those returned by the checked square/multiply calls. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers Maps.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_finish_execute
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_pair_multiply C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_separate_numeric C.jet_secp_square_execution C.jet_secp_multiply_literal_spec
 C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program C.jet_secp_canonical_zero
 C.jet_secp_double_coordinate_numeric
 C.jet_secp_root_literal C.jet_secp_root_square_loop C.jet_secp_root_square_bridge
 C.jet_secp_root_stage C.jet_secp_root_tower_step C.jet_secp_root_chain_owned.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_words field_pair_product root_stage_words literal_fe_square literal_fe_multiply literal_fe_squares.
Local Notation sq := (@literal_fe_square Alg.CoreFunSem).
Local Notation mul := (@literal_fe_multiply Alg.CoreFunSem).
Local Notation squares n := (@literal_fe_squares n Alg.CoreFunSem).

Definition root_words_match w (a : Ty.tySem (Word 8)) :=
 square_input_bounds w /\ radix_value w mod feP=@toZ (WordToZ 8) a mod feP.

Lemma root_square_match w a : root_words_match w a -> root_words_match (square_words w) (sq a).
Proof.
 intros [BW HW];split;[apply square_result_reusable;exact BW|].
 apply double_match_mod;apply double_square_matches;assumption.
Qed.
Lemma root_squares_match n w a : root_words_match w a -> root_words_match (root_square_words n w) (squares n a).
Proof. intros [BW HW];apply root_square_words_match;assumption. Qed.

Local Transparent field_pair_product.
Lemma root_pair_match w v a b : root_words_match w a -> root_words_match v b ->
 root_words_match (field_pair_product w v) (mul (b,a)).
Proof.
 intros [BW HW] [BV HV];split.
 - intros i HI;unfold field_pair_product.
   pose proof (original_outputs_bounds (field_pair_valuation w v) (field_pair_input_bounds w v BW BV) i HI) as HB.
   destruct (Nat.eqb i 4);lia.
 - assert (HP : radix_value (field_pair_product w v) mod feP=(radix_value w*radix_value v) mod feP).
   { unfold field_pair_product.
     pose proof (original_outputs_product (field_pair_valuation w v) (field_pair_input_bounds w v BW BV)) as HProduct.
     rewrite field_pair_radix_left,field_pair_radix_right,field_prime_matches_normalizer in HProduct;exact HProduct. }
   rewrite HP;apply double_match_mod;rewrite literal_multiply_numeric.
   rewrite (Z.mul_comm (radix_value w) (radix_value v));apply double_residue_product;assumption.
Qed.

Local Opaque field_pair_product.
Local Transparent root_stage_words.
Lemma root_stage_match n w v a b : root_words_match w a -> root_words_match v b ->
 root_words_match (root_stage_words n w v) (mul (b,squares n a)).
Proof.
 intros HW HV;unfold root_stage_words;apply root_pair_match;[apply root_squares_match;exact HW|exact HV].
Qed.
Local Opaque root_stage_words.

Local Transparent literal_fe_squares.
Lemma root_squares_two a : squares 2 a=sq (sq a).
Proof. reflexivity. Qed.
Lemma root_squares_three a : squares 3 a=sq (sq (sq a)).
Proof. reflexivity. Qed.
Local Opaque literal_fe_squares.

Definition root_chain_window w :=
 let x2 := field_pair_product (square_words w) w in
 let x3 := field_pair_product (square_words x2) w in
 let x6 := root_stage_words 3 x3 x3 in
 let x9 := root_stage_words 3 x6 x3 in
 let x11 := root_stage_words 2 x9 x2 in
 let x22 := root_stage_words 11 x11 x11 in
 let x44 := root_stage_words 22 x22 x22 in
 let x88 := root_stage_words 44 x44 x44 in
 let x176 := root_stage_words 88 x88 x88 in
 let x220 := root_stage_words 44 x176 x44 in
 let x223 := root_stage_words 3 x220 x3 in
 (x2,root_stage_words 23 x223 x22).

Lemma root_chain_final_x2 w2 w3 :
 (root_chain_final w2 w3)!jets_secp._x2=Some w2.
Proof. reflexivity. Qed.
Lemma root_chain_final_t1 w :
 let w2 := field_pair_product (square_words w) w in
 let w3 := field_pair_product (square_words w2) w in
 (root_chain_final w2 w3)!jets_secp._t1=Some (snd (root_chain_window w)).
Proof. reflexivity. Qed.

Theorem root_chain_window_matches w x : root_words_match w x ->
 root_words_match (fst (root_chain_window w)) (fst (@literal_fe_tower Alg.CoreFunSem x)) /\
 root_words_match (root_square_words 5 (snd (root_chain_window w))) (snd (@literal_fe_tower Alg.CoreFunSem x)).
Proof.
 intro HW.
 pose proof (root_pair_match (square_words w) w (sq x) x (root_square_match w x HW) HW) as H2.
 pose proof (root_pair_match _ w _ x (root_square_match _ _ H2) HW) as H3.
 pose proof (root_stage_match 3 _ _ _ _ H3 H3) as H6;rewrite root_squares_three in H6.
 pose proof (root_stage_match 3 _ _ _ _ H6 H3) as H9;rewrite root_squares_three in H9.
 pose proof (root_stage_match 2 _ _ _ _ H9 H2) as H11;rewrite root_squares_two in H11.
 pose proof (root_stage_match 11 _ _ _ _ H11 H11) as H22.
 pose proof (root_stage_match 22 _ _ _ _ H22 H22) as H44.
 pose proof (root_stage_match 44 _ _ _ _ H44 H44) as H88.
 pose proof (root_stage_match 88 _ _ _ _ H88 H88) as H176.
 pose proof (root_stage_match 44 _ _ _ _ H176 H44) as H220.
 pose proof (root_stage_match 3 _ _ _ _ H220 H3) as H223;rewrite root_squares_three in H223.
 pose proof (root_stage_match 23 _ _ _ _ H223 H22) as HT.
 rewrite literal_fe_tower_step;split;[exact H2|exact (root_squares_match 5 _ _ HT)].
Qed.

Definition literal_root_candidate (x : Ty.tySem (Word 8)) :=
 let t := @literal_fe_tower Alg.CoreFunSem x in sq (sq (mul (fst t,sq (snd t)))).
Definition root_chain_candidate w :=
 let t := root_chain_window w in
 square_words (square_words (field_pair_product (root_square_words 6 (snd t)) (fst t))).

Theorem root_chain_candidate_matches w x : root_words_match w x ->
 root_words_match (root_chain_candidate w) (literal_root_candidate x).
Proof.
 intro HW;destruct (root_chain_window_matches w x HW) as [H2 HT].
 pose proof (root_square_match _ _ HT) as H6.
 change (root_words_match (root_square_words 6 (snd (root_chain_window w)))
   (sq (snd (@literal_fe_tower Alg.CoreFunSem x)))) in H6.
 exact (root_square_match _ _ (root_square_match _ _ (root_pair_match _ _ _ _ H6 H2))).
Qed.

Theorem root_chain_check_matches w x : root_words_match w x ->
 root_words_match (square_words (root_chain_candidate w)) (sq (literal_root_candidate x)).
Proof. intro HW;apply root_square_match;apply root_chain_candidate_matches;exact HW. Qed.

Local Opaque literal_root_candidate literal_fe_tower literal_fe_negate literal_fe_add canonical_fe_is_zero.
Lemma literal_root_result_step (x : Ty.tySem (Word 8)) :
 @literal_fe_square_root Alg.CoreFunSem x=
 match @canonical_fe_is_zero Alg.CoreFunSem
  (@literal_fe_add Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem x,sq (literal_root_candidate x))) with
 | inl _ => inl tt
 | inr _ => inr (literal_root_candidate x)
 end.
Proof.
 Local Transparent literal_root_candidate.
 unfold literal_root_candidate;exact (literal_fe_square_root_step x).
Qed.

(** The optimized square's actual symbolic schedule equals multiplication
    on the diagonal. The signed shift is justified, not silently replaced. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_checkpoint_bridge.
Require Import C.jet_secp_multiply_checkpoint_ops.
Require Import C.jet_secp_multiply_secondvalues_arithmetic C.jet_secp_multiply_third_arithmetic
  C.jet_secp_multiply_fourth_arithmetic C.jet_secp_multiply_fifth_arithmetic C.jet_secp_multiply_finish_values.
Require Import C.jet_secp_square_accum_algebra C.jet_secp_square_columns C.jet_secp_square_schedule.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section Values.
Variable rho : nat -> int64.
Variable beta : nat -> block * Z.
Hypothesis HB : square_input_bounds rho.

Lemma sq_c8_den : pair_den rho beta sq_c8 = first_c_machine (diagonal rho).
Proof. reflexivity. Qed.
Lemma sq_d3_den : pair_den rho beta sq_d3 = first_d_machine (diagonal rho).
Proof.
  unfold sq_d3; rewrite sx_accum_machine, sx_product_machine.
  change (machine_accum (machine_product (twice (rho 0%nat)) (rho 3%nat))
    (twice (rho 1%nat)) (rho 2%nat) = first_d_machine (diagonal rho)).
  apply square_column3; exact HB.
Qed.
Lemma sq_fold3_den : pair_den rho beta sq_fold3 = first_fold_machine (diagonal rho).
Proof.
  unfold sq_fold3, first_fold_machine; rewrite sx_accum_machine, sq_d3_den.
  change (machine_accum (first_d_machine (diagonal rho)) (Int64.repr 68719492368)
    (fst (pair_den rho beta sq_c8)) = first_fold_machine (diagonal rho)).
  rewrite sq_c8_den; reflexivity.
Qed.
Lemma sq_t3_den : den rho beta sq_t3 = Vlong (first_t3_machine (diagonal rho)).
Proof.
  change (Vlong (Int64.and (fst (pair_den rho beta sq_fold3)) (Int64.repr 4503599627370495)) =
    Vlong (first_t3_machine (diagonal rho))).
  rewrite sq_fold3_den; reflexivity.
Qed.
Lemma sq_c8_hi_den : pair_den rho beta sq_c8_hi = first_final_c_machine (diagonal rho).
Proof. unfold sq_c8_hi; rewrite sx_shift64_machine, sq_c8_den; reflexivity. Qed.
Lemma sq_d3_hi_den : pair_den rho beta sq_d3_hi = first_final_d_machine (diagonal rho).
Proof. unfold sq_d3_hi; rewrite sx_shift52_machine, sq_fold3_den; reflexivity. Qed.
Lemma sq_fold4_den : pair_den rho beta sq_fold4 = original_second_fold (diagonal rho).
Proof.
  unfold sq_fold4, sq_d4; rewrite !sx_accum_machine, sq_d3_hi_den.
  change (machine_accum
    (machine_accum (machine_accum (machine_accum (first_final_d_machine (diagonal rho))
      (rho 0%nat) (twice (rho 4%nat))) (twice (rho 1%nat)) (rho 3%nat)) (rho 2%nat) (rho 2%nat))
    (Int64.shl (Int64.repr 68719492368) (Int64.repr 12)) (fst (pair_den rho beta sq_c8_hi)) =
    original_second_fold (diagonal rho)).
  rewrite sq_c8_hi_den; apply square_column4; exact HB.
Qed.
Lemma sq_d4_hi_den : pair_den rho beta sq_d4_hi = original_second_final (diagonal rho).
Proof. unfold sq_d4_hi; rewrite sx_shift52_machine, sq_fold4_den; reflexivity. Qed.
Lemma sq_tx_den : den rho beta sq_tx = Vlong (original_second_tx (diagonal rho)).
Proof.
  change (Vlong (Int64.shr (Int64.and (fst (pair_den rho beta sq_fold4))
    (Int64.repr 4503599627370495)) (Int64.repr 48)) = Vlong (original_second_tx (diagonal rho))).
  rewrite sq_fold4_den, Int64.shr_shru_positive.
  - reflexivity.
  - apply Int64.and_positive; change (4503599627370495 >= 0); lia.
Qed.
Lemma sq_t4_den : den rho beta sq_t4 = Vlong (original_second_t4 (diagonal rho)).
Proof.
  change (Vlong (Int64.and (Int64.and (fst (pair_den rho beta sq_fold4))
    (Int64.repr 4503599627370495))
    (Int64.shru (Int64.repr 4503599627370495) (Int64.repr 4))) =
    Vlong (original_second_t4 (diagonal rho))).
  rewrite sq_fold4_den; reflexivity.
Qed.
Lemma sq_d5_den : pair_den rho beta sq_d5 = original_third_fold_d (diagonal rho).
Proof.
  unfold sq_d5; rewrite !sx_accum_machine, sq_d4_hi_den.
  change (machine_accum (machine_accum (original_second_final (diagonal rho))
    (rho 1%nat) (twice (rho 4%nat))) (twice (rho 2%nat)) (rho 3%nat) =
    original_third_fold_d (diagonal rho)).
  apply square_column5; exact HB.
Qed.
Lemma sq_d5_hi_den : pair_den rho beta sq_d5_hi = original_third_final_d (diagonal rho).
Proof. unfold sq_d5_hi; rewrite sx_shift52_machine, sq_d5_den; reflexivity. Qed.
Lemma sq_u0_den : den rho beta sq_u0 = Vlong (original_third_u0 (diagonal rho)).
Proof.
  change (Vlong (Int64.or (Int64.shl (Int64.and (fst (pair_den rho beta sq_d5))
    (Int64.repr 4503599627370495)) (Int64.repr 4)) (il (den rho beta sq_tx))) =
    Vlong (original_third_u0 (diagonal rho))).
  rewrite sq_d5_den, sq_tx_den; reflexivity.
Qed.
Lemma sq_c0_den : pair_den rho beta sq_c0 = original_third_fold_c (diagonal rho).
Proof.
  unfold sq_c0; rewrite sx_accum_machine, sx_product_machine.
  change (machine_accum (machine_product (rho 0%nat) (rho 0%nat))
    (il (den rho beta sq_u0)) (Int64.shru (Int64.repr 68719492368) (Int64.repr 4)) =
    original_third_fold_c (diagonal rho)).
  rewrite sq_u0_den; reflexivity.
Qed.
Lemma sq_c0_hi_den : pair_den rho beta sq_c0_hi = original_third_final_c (diagonal rho).
Proof. unfold sq_c0_hi; rewrite sx_shift52_machine, sq_c0_den; reflexivity. Qed.
Lemma sq_r0_den : den rho beta sq_r0 = Vlong (original_third_r0 (diagonal rho)).
Proof.
  change (Vlong (Int64.and (fst (pair_den rho beta sq_c0)) (Int64.repr 4503599627370495)) =
    Vlong (original_third_r0 (diagonal rho))).
  rewrite sq_c0_den; reflexivity.
Qed.

Lemma sq_c1_den : pair_den rho beta sq_c1 = original_fourth_base_c (diagonal rho).
Proof.
  unfold sq_c1; rewrite sx_accum_machine, sq_c0_hi_den.
  change (machine_accum (original_third_final_c (diagonal rho))
    (twice (rho 0%nat)) (rho 1%nat) = original_fourth_base_c (diagonal rho)).
  apply square_column1; exact HB.
Qed.
Lemma sq_d6_den : pair_den rho beta sq_d6 = original_fourth_fold_d (diagonal rho).
Proof.
  unfold sq_d6; rewrite !sx_accum_machine, sq_d5_hi_den.
  change (machine_accum (machine_accum (original_third_final_d (diagonal rho))
    (rho 2%nat) (twice (rho 4%nat))) (rho 3%nat) (rho 3%nat) = original_fourth_fold_d (diagonal rho)).
  apply square_column6; exact HB.
Qed.
Lemma sq_fold1_den : pair_den rho beta sq_fold1 = original_fourth_fold_c (diagonal rho).
Proof.
  unfold sq_fold1; rewrite sx_accum_machine, sq_c1_den.
  change (machine_accum (original_fourth_base_c (diagonal rho))
    (Int64.and (fst (pair_den rho beta sq_d6)) (Int64.repr 4503599627370495))
    (Int64.repr 68719492368) = original_fourth_fold_c (diagonal rho)).
  rewrite sq_d6_den; reflexivity.
Qed.
Lemma sq_c1_hi_den : pair_den rho beta sq_c1_hi = original_fourth_final_c (diagonal rho).
Proof. unfold sq_c1_hi; rewrite sx_shift52_machine, sq_fold1_den; reflexivity. Qed.
Lemma sq_d6_hi_den : pair_den rho beta sq_d6_hi = original_fourth_final_d (diagonal rho).
Proof. unfold sq_d6_hi; rewrite sx_shift52_machine, sq_d6_den; reflexivity. Qed.
Lemma sq_r1_den : den rho beta sq_r1 = Vlong (original_fourth_r1 (diagonal rho)).
Proof.
  change (Vlong (Int64.and (fst (pair_den rho beta sq_fold1)) (Int64.repr 4503599627370495)) =
    Vlong (original_fourth_r1 (diagonal rho))).
  rewrite sq_fold1_den; reflexivity.
Qed.
Lemma sq_c2_den : pair_den rho beta sq_c2 = original_fifth_base_c (diagonal rho).
Proof.
  unfold sq_c2; rewrite !sx_accum_machine, sq_c1_hi_den.
  change (machine_accum (machine_accum (original_fourth_final_c (diagonal rho))
    (twice (rho 0%nat)) (rho 2%nat)) (rho 1%nat) (rho 1%nat) = original_fifth_base_c (diagonal rho)).
  apply square_column2; exact HB.
Qed.
Lemma sq_d7_den : pair_den rho beta sq_d7 = original_fifth_fold_d (diagonal rho).
Proof.
  unfold sq_d7; rewrite sx_accum_machine, sq_d6_hi_den.
  change (machine_accum (original_fourth_final_d (diagonal rho)) (rho 3%nat) (twice (rho 4%nat)) =
    original_fifth_fold_d (diagonal rho)).
  apply square_column7; exact HB.
Qed.
Lemma sq_fold2_den : pair_den rho beta sq_fold2 = original_fifth_fold_c (diagonal rho).
Proof.
  unfold sq_fold2; rewrite sx_accum_machine, sq_c2_den.
  change (machine_accum (original_fifth_base_c (diagonal rho)) (Int64.repr 68719492368)
    (fst (pair_den rho beta sq_d7)) = original_fifth_fold_c (diagonal rho)).
  rewrite sq_d7_den; reflexivity.
Qed.
Lemma sq_c2_hi_den : pair_den rho beta sq_c2_hi = original_fifth_final_c (diagonal rho).
Proof. unfold sq_c2_hi; rewrite sx_shift52_machine, sq_fold2_den; reflexivity. Qed.
Lemma sq_d7_hi_den : pair_den rho beta sq_d7_hi = original_fifth_final_d (diagonal rho).
Proof. unfold sq_d7_hi; rewrite sx_shift64_machine, sq_d7_den; reflexivity. Qed.
Lemma sq_r2_den : den rho beta sq_r2 = Vlong (original_fifth_r2 (diagonal rho)).
Proof.
  change (Vlong (Int64.and (fst (pair_den rho beta sq_fold2)) (Int64.repr 4503599627370495)) =
    Vlong (original_fifth_r2 (diagonal rho))).
  rewrite sq_fold2_den; reflexivity.
Qed.
Lemma sq_c3_den : pair_den rho beta sq_c3 = finish_fold_c_machine
  (original_fifth_final_c (diagonal rho)) (original_fifth_final_d (diagonal rho))
  (first_t3_machine (diagonal rho)).
Proof.
  unfold sq_c3; rewrite sx_accum_word_machine, sx_accum_machine, sq_c2_hi_den.
  change (machine_accum_word
    (machine_accum (original_fifth_final_c (diagonal rho))
      (Int64.shl (Int64.repr 68719492368) (Int64.repr 12)) (fst (pair_den rho beta sq_d7_hi)))
    (il (den rho beta sq_t3)) = finish_fold_c_machine
      (original_fifth_final_c (diagonal rho)) (original_fifth_final_d (diagonal rho))
      (first_t3_machine (diagonal rho))).
  rewrite sq_d7_hi_den, sq_t3_den; reflexivity.
Qed.
Lemma sq_r3_den : den rho beta sq_r3 = Vlong (finish_r3_machine
  (original_fifth_final_c (diagonal rho)) (original_fifth_final_d (diagonal rho))
  (first_t3_machine (diagonal rho))).
Proof.
  unfold sq_r3.
  change (Vlong (Int64.and (fst (pair_den rho beta sq_c3)) (Int64.repr 4503599627370495)) =
    Vlong (finish_r3_machine (original_fifth_final_c (diagonal rho))
      (original_fifth_final_d (diagonal rho)) (first_t3_machine (diagonal rho)))).
  rewrite sq_c3_den; reflexivity.
Qed.
Lemma sq_r4_den : den rho beta sq_r4 = Vlong (finish_r4_machine
  (original_fifth_final_c (diagonal rho)) (original_fifth_final_d (diagonal rho))
  (first_t3_machine (diagonal rho)) (original_second_t4 (diagonal rho))).
Proof.
  change (Vlong (Int64.add (fst (pair_den rho beta (sx_shift52 sq_c3)))
    (il (den rho beta sq_t4))) = Vlong (finish_r4_machine
      (original_fifth_final_c (diagonal rho)) (original_fifth_final_d (diagonal rho))
      (first_t3_machine (diagonal rho)) (original_second_t4 (diagonal rho)))).
  rewrite sx_shift52_machine, sq_c3_den, sq_t4_den; reflexivity.
Qed.

End Values.

(** Numeric result and writer bounds of the actual optimized square output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_secp_multiply_finish_execute C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_schedule C.jet_secp_square_denote C.jet_secp_square_source_list.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_limbs sq_r0 sq_r1 sq_r2 sq_r3 sq_r4.

Definition square_words rho := original_finish_words (diagonal rho).
Lemma square_output_den rho beta : square_input_bounds rho -> forall i, (i < 5)%nat ->
  den rho beta (nth i square_limbs (XLv 0)) = Vlong (square_words rho i).
Proof.
  intros HB i HI; rewrite original_square_symbolic_output.
  destruct i as [|[|[|[|[|i]]]]]; try lia.
  - change (den rho beta sq_r0 = Vlong (square_words rho 0%nat)); apply sq_r0_den; exact HB.
  - change (den rho beta sq_r1 = Vlong (square_words rho 1%nat)); apply sq_r1_den; exact HB.
  - change (den rho beta sq_r2 = Vlong (square_words rho 2%nat)); apply sq_r2_den; exact HB.
  - change (den rho beta sq_r3 = Vlong (square_words rho 3%nat)); apply sq_r3_den; exact HB.
  - change (den rho beta sq_r4 = Vlong (square_words rho 4%nat)); apply sq_r4_den; exact HB.
Qed.
Lemma diagonal_radix rho : radix_value (diagonal rho) = radix_value rho.
Proof. reflexivity. Qed.
Lemma diagonal_second_radix rho : radix_value (second_input (diagonal rho)) = radix_value rho.
Proof. reflexivity. Qed.
Theorem square_output_numeric rho : square_input_bounds rho ->
  radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime.
Proof.
  intro HB; unfold square_words.
  rewrite original_outputs_product by (apply diagonal_input_bounds; exact HB).
  rewrite diagonal_radix, diagonal_second_radix; reflexivity.
Qed.
Theorem square_output_bounds rho : square_input_bounds rho -> forall i, (i < 5)%nat ->
  0 <= Int64.unsigned (square_words rho i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496.
Proof. intro HB; apply original_outputs_bounds; apply diagonal_input_bounds; exact HB. Qed.

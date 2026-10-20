(** The actual C body's five output limbs represent the input product mod p. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events Values.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_checkpoint_prefix C.jet_secp_multiply_checkpoint_bridge C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_multiply_first_arithmetic C.jet_secp_multiply_secondvalues_accum C.jet_secp_multiply_secondvalues_arithmetic.
Require Import C.jet_secp_multiply_third_arithmetic C.jet_secp_multiply_fourth_arithmetic C.jet_secp_multiply_fifth_arithmetic.
Require Import C.jet_secp_multiply_finish_execute C.jet_secp_multiply_finish_arithmetic.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition radix_value (words : nat -> int64) := Int64.unsigned (words 0%nat) + radix * Int64.unsigned (words 1%nat) +
  radix ^ 2 * Int64.unsigned (words 2%nat) + radix ^ 3 * Int64.unsigned (words 3%nat) + radix ^ 4 * Int64.unsigned (words 4%nat).
Definition second_input (rho : nat -> int64) n := rho (n + 5)%nat.
Definition original_columns (rho : nat -> int64) := mkcolumns
  (Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 5%nat)) (column1 rho) (column2 rho)
  (column3 rho) (column4 rho) (column5 rho) (column6 rho) (column7 rho) (column8 rho).

Local Opaque radix.
Lemma original_columns_product rho : columns_value (original_columns rho) = radix_value rho * radix_value (second_input rho).
Proof.
  unfold columns_value, original_columns, radix_value, second_input.
  cbn [p0 p1 p2 p3 p4 p5 p6 p7 p8 Nat.add].
  unfold column1, column2, column3, column4, column5, column6, column7, column8,
    fourth_pairs_c, fourth_pairs_d, fifth_pairs_c, fifth_pairs_d, second_pairs, third_pairs.
  cbn [products]; ring.
Qed.
Local Transparent radix.
Lemma third_c_model rho : third_integer_c rho = c0 (original_columns rho).
Proof. reflexivity. Qed.
Lemma fourth_c_model rho : fourth_integer_c rho = c1 (original_columns rho).
Proof. reflexivity. Qed.
Lemma fifth_d_model rho : fifth_integer_d rho = d7 (original_columns rho).
Proof. reflexivity. Qed.
Lemma fifth_c_model rho : fifth_integer_c rho = c2 (original_columns rho).
Proof.
  unfold fifth_integer_c, fifth_integer_base_c.
  rewrite fourth_c_model, fifth_d_model.
  unfold c2. reflexivity.
Qed.
Local Opaque first_t3_machine.
Lemma first_t3_model rho : field_input_bounds rho -> Int64.unsigned (first_t3_machine rho) = t3 (original_columns rho).
Proof.
  intro HB; unfold t3, d3, original_columns; cbn [p3 p8].
  change (Int64.unsigned (first_t3_machine rho) =
    (column3 rho + 68719492368 * (column8 rho mod Int64.modulus)) mod 4503599627370496).
  exact (first_t3_value rho HB).
Qed.
Lemma finish_c_model rho : field_input_bounds rho -> finish_integer_c rho = c3 (original_columns rho).
Proof.
  intro HB.
  unfold finish_integer_c, finish_integer_base_c.
  rewrite fifth_c_model, fifth_d_model, (first_t3_model rho HB).
  unfold c3, radix, reduction, carrier.
  reflexivity.
Qed.
Lemma second_t4_model rho : field_input_bounds rho -> Int64.unsigned (original_second_t4 rho) = t4 (original_columns rho).
Proof. intro HB; rewrite (second_t4_value rho HB); reflexivity. Qed.

Lemma original_outputs_reduced rho : field_input_bounds rho -> radix_value (original_finish_words rho) = reduced_value (original_columns rho).
Proof.
  intro HB.
  change (Int64.unsigned (original_third_r0 rho) + radix * Int64.unsigned (original_fourth_r1 rho) +
    radix ^ 2 * Int64.unsigned (original_fifth_r2 rho) + radix ^ 3 * Int64.unsigned (original_finish_r3 rho) +
    radix ^ 4 * Int64.unsigned (original_finish_r4 rho) = reduced_value (original_columns rho)).
  rewrite third_r0_value, fourth_r1_value, fifth_r2_value, finish_r3_value, finish_r4_value by exact HB.
  rewrite third_c_model, fourth_c_model, fifth_c_model, finish_c_model, second_t4_model by exact HB.
  reflexivity.
Qed.
Lemma original_outputs_product rho : field_input_bounds rho ->
  radix_value (original_finish_words rho) mod field_prime = (radix_value rho * radix_value (second_input rho)) mod field_prime.
Proof.
  intro HB; rewrite original_outputs_reduced by exact HB; rewrite columns_modulo, original_columns_product; reflexivity.
Qed.
Lemma original_outputs_bounds rho : field_input_bounds rho -> forall i, (i < 5)%nat ->
  0 <= Int64.unsigned (original_finish_words rho i) < if Nat.eqb i 4 then 562949953421312 else 4503599627370496.
Proof.
  intros HB i HI; destruct i as [|[|[|[|[|i]]]]]; try lia.
  - change (0 <= Int64.unsigned (original_third_r0 rho) < 4503599627370496); apply third_r0_bound.
  - change (0 <= Int64.unsigned (original_fourth_r1 rho) < 4503599627370496); apply fourth_r1_bound.
  - change (0 <= Int64.unsigned (original_fifth_r2 rho) < 4503599627370496); apply fifth_r2_bound.
  - change (0 <= Int64.unsigned (original_finish_r3 rho) < 4503599627370496); apply finish_r3_bound.
  - change (0 <= Int64.unsigned (original_finish_r4 rho) < 562949953421312); apply finish_r4_bound; exact HB.
Qed.

Local Opaque prefix_initial original_finish_checkpoint.
Theorem exec_original_field_body_product rho beta e le m :
  field_input_bounds rho -> rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_fe_mul_inner) E0 le' mf Out_normal /\
    rep rho beta (sregs (original_finish_checkpoint rho)) mf /\
    tmatch rho beta (stemps (original_finish_checkpoint rho)) le' /\
    output_words beta (original_finish_words rho) mf /\
    radix_value (original_finish_words rho) mod field_prime = (radix_value rho * radix_value (second_input rho)) mod field_prime /\
    (forall i, (i < 5)%nat -> 0 <= Int64.unsigned (original_finish_words rho i) <
      if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  intros HB HR HT HE.
  destruct (exec_original_field_body rho beta e le m HR HT HE) as (le' & mf & HX & HRep & HTm & HO & HF).
  exists le', mf; split; [exact HX|]; split; [exact HRep|]; split; [exact HTm|]; split; [exact HO|];
    split; [apply original_outputs_product; exact HB|]; split; [apply original_outputs_bounds; exact HB|exact HF].
Qed.

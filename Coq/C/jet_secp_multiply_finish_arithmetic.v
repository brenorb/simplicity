(** Exact final integer values and no-overflow facts for the real C body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events Values.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_checkpoint_bridge C.jet_secp_multiply_checkpoint_prefix.
Require Import C.jet_secp_multiply_first_arithmetic C.jet_secp_multiply_secondvalues_arithmetic C.jet_secp_multiply_fifth_arithmetic.
Require Import C.jet_secp_multiply_finish_state C.jet_secp_multiply_finish_values C.jet_secp_multiply_finish_word C.jet_secp_multiply_finish_execute.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition finish_integer_base_c rho := fifth_integer_c rho / 4503599627370496 +
  (68719492368 * 4096) * (fifth_integer_d rho / Int64.modulus).
Definition finish_integer_c rho := finish_integer_base_c rho + Int64.unsigned (first_t3_machine rho).
Definition original_finish_base_c rho := finish_base_c_machine (original_fifth_final_c rho) (original_fifth_final_d rho).
Definition original_finish_fold_c rho := finish_fold_c_machine (original_fifth_final_c rho) (original_fifth_final_d rho) (first_t3_machine rho).
Definition original_finish_final_c rho := finish_final_c_machine (original_fifth_final_c rho) (original_fifth_final_d rho) (first_t3_machine rho).
Definition original_finish_r3 rho := finish_r3_machine (original_fifth_final_c rho) (original_fifth_final_d rho) (first_t3_machine rho).
Definition original_finish_r4 rho := finish_r4_machine (original_fifth_final_c rho) (original_fifth_final_d rho) (first_t3_machine rho) (original_second_t4 rho).

Lemma first_t3_bound rho : 0 <= Int64.unsigned (first_t3_machine rho) < 4503599627370496.
Proof. unfold first_t3_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia. Qed.
Lemma finish_d_word_value rho : field_input_bounds rho ->
  Int64.unsigned (fst (original_fifth_final_d rho)) = pair_value (original_fifth_final_d rho).
Proof.
  intro HB; rewrite pair_low_mod64; apply Z.mod_small.
  pose proof (fifth_final_d_bound rho HB); change Int64.modulus with 18446744073709551616; lia.
Qed.
Lemma finish_base_c_value rho : field_input_bounds rho -> pair_value (original_finish_base_c rho) = finish_integer_base_c rho.
Proof.
  intro HB; unfold original_finish_base_c, finish_base_c_machine; rewrite machine_accum_exact.
  - rewrite shifted_reduction_unsigned, finish_d_word_value by exact HB.
    rewrite fifth_final_c_value, fifth_final_d_value by exact HB; reflexivity.
  - rewrite shifted_reduction_unsigned, finish_d_word_value by exact HB.
    pose proof (fifth_final_c_bound rho HB); pose proof (fifth_final_d_bound rho HB).
    change (Int64.modulus * Int64.modulus) with 340282366920938463463374607431768211456; lia.
Qed.
Lemma finish_base_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_finish_base_c rho) < 1267650600228229401496703205376.
Proof.
  intro HB; rewrite finish_base_c_value by exact HB; unfold finish_integer_base_c.
  rewrite <- fifth_final_c_value, <- fifth_final_d_value by exact HB.
  pose proof (fifth_final_c_bound rho HB); pose proof (fifth_final_d_bound rho HB); lia.
Qed.
Lemma finish_fold_c_value rho : field_input_bounds rho -> pair_value (original_finish_fold_c rho) = finish_integer_c rho.
Proof.
  intro HB; unfold original_finish_fold_c, finish_fold_c_machine; rewrite machine_accum_word_exact.
  - change (pair_value (original_finish_base_c rho) + Int64.unsigned (first_t3_machine rho) = finish_integer_c rho).
    rewrite finish_base_c_value by exact HB; reflexivity.
  - change (pair_value (original_finish_base_c rho) + Int64.unsigned (first_t3_machine rho) < 340282366920938463463374607431768211456).
    pose proof (finish_base_c_bound rho HB); pose proof (first_t3_bound rho); lia.
Qed.
Lemma finish_fold_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_finish_fold_c rho) < 1267650600228229401496703205376.
Proof.
  intro HB; rewrite finish_fold_c_value by exact HB; unfold finish_integer_c, finish_integer_base_c.
  rewrite <- fifth_final_c_value, <- fifth_final_d_value by exact HB.
  pose proof (fifth_final_c_bound rho HB); pose proof (fifth_final_d_bound rho HB); pose proof (first_t3_bound rho); lia.
Qed.
Lemma finish_final_c_value rho : field_input_bounds rho -> pair_value (original_finish_final_c rho) = finish_integer_c rho / 4503599627370496.
Proof.
  intro HB; unfold original_finish_final_c, finish_final_c_machine; rewrite machine_shift52_value.
  change (pair_value (original_finish_fold_c rho) / 4503599627370496 = finish_integer_c rho / 4503599627370496).
  rewrite finish_fold_c_value by exact HB; reflexivity.
Qed.
Lemma finish_final_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_finish_final_c rho) < 281474976710656.
Proof.
  intro HB; pose proof (finish_fold_c_bound rho HB).
  unfold original_finish_final_c, finish_final_c_machine; rewrite machine_shift52_value.
  change (0 <= pair_value (original_finish_fold_c rho) / 4503599627370496 < 281474976710656).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma finish_final_c_word_value rho : field_input_bounds rho ->
  Int64.unsigned (fst (original_finish_final_c rho)) = pair_value (original_finish_final_c rho).
Proof.
  intro HB; rewrite pair_low_mod64; apply Z.mod_small.
  pose proof (finish_final_c_bound rho HB); change Int64.modulus with 18446744073709551616; lia.
Qed.
Lemma finish_r3_value rho : field_input_bounds rho -> Int64.unsigned (original_finish_r3 rho) = finish_integer_c rho mod 4503599627370496.
Proof.
  intro HB; unfold original_finish_r3, finish_r3_machine; rewrite machine_mask52_value.
  change (Int64.unsigned (fst (original_finish_fold_c rho)) mod 4503599627370496 = finish_integer_c rho mod 4503599627370496).
  rewrite pair_low_mod52, finish_fold_c_value by exact HB; reflexivity.
Qed.
Lemma finish_r3_bound rho : 0 <= Int64.unsigned (original_finish_r3 rho) < 4503599627370496.
Proof. unfold original_finish_r3, finish_r3_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia. Qed.
Lemma finish_r4_value rho : field_input_bounds rho -> Int64.unsigned (original_finish_r4 rho) =
  finish_integer_c rho / 4503599627370496 + Int64.unsigned (original_second_t4 rho).
Proof.
  intro HB; unfold original_finish_r4, finish_r4_machine; rewrite add_u64_exact.
  - change (Int64.unsigned (fst (original_finish_final_c rho)) + Int64.unsigned (original_second_t4 rho) =
      finish_integer_c rho / 4503599627370496 + Int64.unsigned (original_second_t4 rho)).
    rewrite finish_final_c_word_value, finish_final_c_value by exact HB; reflexivity.
  - change (Int64.unsigned (fst (original_finish_final_c rho)) + Int64.unsigned (original_second_t4 rho) < 18446744073709551616).
    rewrite finish_final_c_word_value by exact HB.
    pose proof (finish_final_c_bound rho HB); pose proof (second_t4_bound rho HB); lia.
Qed.
Lemma finish_r4_bound rho : field_input_bounds rho -> 0 <= Int64.unsigned (original_finish_r4 rho) < 562949953421312.
Proof.
  intro HB; rewrite finish_r4_value by exact HB; rewrite <- finish_final_c_value by exact HB.
  pose proof (finish_final_c_bound rho HB); pose proof (second_t4_bound rho HB); lia.
Qed.

Local Opaque xstmt prefix_initial original_finish_checkpoint.
Theorem exec_original_field_body_integer rho beta e le m :
  field_input_bounds rho -> rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_fe_mul_inner) E0 le' mf Out_normal /\
    rep rho beta (sregs (original_finish_checkpoint rho)) mf /\
    tmatch rho beta (stemps (original_finish_checkpoint rho)) le' /\
    output_words beta (original_finish_words rho) mf /\
    Int64.unsigned (original_finish_r3 rho) = finish_integer_c rho mod 4503599627370496 /\
    Int64.unsigned (original_finish_r4 rho) = finish_integer_c rho / 4503599627370496 + Int64.unsigned (original_second_t4 rho) /\
    0 <= Int64.unsigned (original_finish_r3 rho) < 4503599627370496 /\
    0 <= Int64.unsigned (original_finish_r4 rho) < 562949953421312 /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  intros HB HR HT HE.
  destruct (exec_original_field_body rho beta e le m HR HT HE) as (le' & mf & HX & HRep & HTm & HO & HF).
  exists le', mf; split; [exact HX|]; split; [exact HRep|]; split; [exact HTm|]; split; [exact HO|];
    split; [apply finish_r3_value; exact HB|]; split; [apply finish_r4_value; exact HB|];
    split; [apply finish_r3_bound|]; split; [apply finish_r4_bound; exact HB|exact HF].
Qed.

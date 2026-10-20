(** Exact integer bridge through the original r[2] store and following shift. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events Values.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage.
Require Import C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_checkpoint_bridge C.jet_secp_multiply_checkpoint_prefix.
Require Import C.jet_secp_multiply_first_arithmetic C.jet_secp_multiply_secondvalues_accum C.jet_secp_multiply_secondvalues_arithmetic C.jet_secp_multiply_third_arithmetic C.jet_secp_multiply_fourth_arithmetic.
Require Import C.jet_secp_multiply_fifth_state C.jet_secp_multiply_fifth_values C.jet_secp_multiply_fifth_execute.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fifth_pairs_c (rho : nat -> int64) := [(rho 0%nat, rho 7%nat); (rho 1%nat, rho 6%nat); (rho 2%nat, rho 5%nat)].
Definition fifth_pairs_d (rho : nat -> int64) := [(rho 3%nat, rho 9%nat); (rho 4%nat, rho 8%nat)].
Definition column2 rho := products (fifth_pairs_c rho).
Definition column7 rho := products (fifth_pairs_d rho).
Definition fifth_integer_d rho := fourth_integer_d rho / 4503599627370496 + column7 rho.
Definition fifth_integer_base_c rho := fourth_integer_c rho / 4503599627370496 + column2 rho.
Definition fifth_integer_c rho := fifth_integer_base_c rho + 68719492368 * (fifth_integer_d rho mod Int64.modulus).
Definition original_fifth_base_c rho := fifth_base_c_machine rho (original_fourth_final_c rho).
Definition original_fifth_fold_d rho := fifth_fold_d_machine rho (original_fourth_final_d rho).
Definition original_fifth_before rho := fifth_before_machine rho (original_fourth_final_d rho).
Definition original_fifth_fold_c rho := fifth_fold_c_machine rho (original_fourth_final_c rho) (original_fourth_final_d rho).
Definition original_fifth_final_c rho := fifth_final_c_machine rho (original_fourth_final_c rho) (original_fourth_final_d rho).
Definition original_fifth_final_d rho := fifth_final_d_machine rho (original_fourth_final_d rho).
Definition original_fifth_r2 rho := fifth_r2_machine rho (original_fourth_final_c rho) (original_fourth_final_d rho).

Lemma fifth_pairs_c56 rho : field_input_bounds rho -> Forall pair56 (fifth_pairs_c rho).
Proof. intro HB; unfold fifth_pairs_c; repeat constructor. all: cbn [fst snd]; apply (every_input56 rho HB); lia. Qed.
Lemma fifth_pairs_d56 rho : field_input_bounds rho -> Forall pair56 (fifth_pairs_d rho).
Proof. intro HB; unfold fifth_pairs_d; repeat constructor. all: cbn [fst snd]; apply (every_input56 rho HB); lia. Qed.
Lemma column2_bound rho : field_input_bounds rho -> 0 <= column2 rho <= 15576890575604482885591488987660288.
Proof. intro HB; exact (products56_bound (fifth_pairs_c rho) (fifth_pairs_c56 rho HB)). Qed.
Lemma column7_bound rho : field_input_bounds rho -> 0 <= column7 rho <= 10384593717069655257060992658440192.
Proof. intro HB; exact (products56_bound (fifth_pairs_d rho) (fifth_pairs_d56 rho HB)). Qed.

Local Opaque machine_accum.
Lemma pair_low_mod64 s : Int64.unsigned (fst s) = pair_value s mod Int64.modulus.
Proof.
  apply Z.mod_unique with (Int64.unsigned (snd s));
    [left; apply Int64.unsigned_range|unfold pair_value; ring].
Qed.

Lemma fifth_c_as_accumulate rho c : fifth_base_c_machine rho c = accumulate c (fifth_pairs_c rho).
Proof. reflexivity. Qed.
Lemma fifth_d_as_accumulate rho d : fifth_fold_d_machine rho d = accumulate d (fifth_pairs_d rho).
Proof. reflexivity. Qed.
Lemma fifth_base_c_value rho : field_input_bounds rho -> pair_value (original_fifth_base_c rho) = fifth_integer_base_c rho.
Proof.
  intro HB; unfold original_fifth_base_c; rewrite fifth_c_as_accumulate, accumulate_exact.
  - unfold fifth_integer_base_c; rewrite fourth_final_c_value by exact HB; reflexivity.
  - pose proof (fourth_final_c_bound rho HB); pose proof (column2_bound rho HB).
    change (pair_value (original_fourth_final_c rho) + column2 rho < 340282366920938463463374607431768211456); lia.
Qed.
Lemma fifth_base_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fifth_base_c rho) < 20769187434139310514121985316880384.
Proof.
  intro HB; rewrite fifth_base_c_value by exact HB; unfold fifth_integer_base_c.
  rewrite <- fourth_final_c_value by exact HB; pose proof (fourth_final_c_bound rho HB); pose proof (column2_bound rho HB); lia.
Qed.
Lemma fifth_fold_d_value rho : field_input_bounds rho -> pair_value (original_fifth_fold_d rho) = fifth_integer_d rho.
Proof.
  intro HB; unfold original_fifth_fold_d; rewrite fifth_d_as_accumulate, accumulate_exact.
  - unfold fifth_integer_d; rewrite fourth_final_d_value by exact HB; reflexivity.
  - pose proof (fourth_final_d_bound rho HB); pose proof (column7_bound rho HB).
    change (pair_value (original_fourth_final_d rho) + column7 rho < 340282366920938463463374607431768211456); lia.
Qed.
Lemma fifth_fold_d_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fifth_fold_d rho) < 20769187434139310514121985316880384.
Proof.
  intro HB; rewrite fifth_fold_d_value by exact HB; unfold fifth_integer_d.
  rewrite <- fourth_final_d_value by exact HB; pose proof (fourth_final_d_bound rho HB); pose proof (column7_bound rho HB); lia.
Qed.
Lemma fifth_before_value rho : field_input_bounds rho -> Int64.unsigned (original_fifth_before rho) = fifth_integer_d rho mod Int64.modulus.
Proof.
  intro HB; unfold original_fifth_before, fifth_before_machine.
  change (Int64.unsigned (fst (original_fifth_fold_d rho)) = fifth_integer_d rho mod Int64.modulus).
  rewrite pair_low_mod64, fifth_fold_d_value by exact HB; reflexivity.
Qed.
Lemma fifth_before_bound rho : 0 <= Int64.unsigned (original_fifth_before rho) < 18446744073709551616.
Proof. apply Int64.unsigned_range. Qed.
Lemma fifth_fold_c_value rho : field_input_bounds rho -> pair_value (original_fifth_fold_c rho) = fifth_integer_c rho.
Proof.
  intro HB; unfold original_fifth_fold_c, fifth_fold_c_machine; rewrite machine_accum_exact.
  - change (pair_value (original_fifth_base_c rho) + 68719492368 * Int64.unsigned (original_fifth_before rho) = fifth_integer_c rho).
    rewrite fifth_base_c_value, fifth_before_value by exact HB; reflexivity.
  - change (pair_value (original_fifth_base_c rho) + 68719492368 * Int64.unsigned (original_fifth_before rho) < 340282366920938463463374607431768211456).
    pose proof (fifth_base_c_bound rho HB); pose proof (fifth_before_bound rho); lia.
Qed.
Lemma fifth_fold_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fifth_fold_c rho) < 41538374868278621028243970633760768.
Proof.
  intro HB; rewrite fifth_fold_c_value by exact HB; unfold fifth_integer_c.
  rewrite <- fifth_base_c_value, <- fifth_before_value by exact HB.
  pose proof (fifth_base_c_bound rho HB); pose proof (fifth_before_bound rho); lia.
Qed.
Lemma fifth_final_c_value rho : field_input_bounds rho -> pair_value (original_fifth_final_c rho) = fifth_integer_c rho / 4503599627370496.
Proof.
  intro HB; unfold original_fifth_final_c, fifth_final_c_machine; rewrite machine_shift52_value.
  change (pair_value (original_fifth_fold_c rho) / 4503599627370496 = fifth_integer_c rho / 4503599627370496).
  rewrite fifth_fold_c_value by exact HB; reflexivity.
Qed.
Lemma fifth_final_d_value rho : field_input_bounds rho -> pair_value (original_fifth_final_d rho) = fifth_integer_d rho / Int64.modulus.
Proof.
  intro HB; unfold original_fifth_final_d, fifth_final_d_machine; rewrite machine_shift64_value.
  change (pair_value (original_fifth_fold_d rho) / Int64.modulus = fifth_integer_d rho / Int64.modulus).
  rewrite fifth_fold_d_value by exact HB; reflexivity.
Qed.
Lemma fifth_final_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fifth_final_c rho) < 9223372036854775808.
Proof.
  intro HB; pose proof (fifth_fold_c_bound rho HB).
  unfold original_fifth_final_c, fifth_final_c_machine; rewrite machine_shift52_value.
  change (0 <= pair_value (original_fifth_fold_c rho) / 4503599627370496 < 9223372036854775808).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma fifth_final_d_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fifth_final_d rho) < 1125899906842624.
Proof.
  intro HB; pose proof (fifth_fold_d_bound rho HB).
  unfold original_fifth_final_d, fifth_final_d_machine; rewrite machine_shift64_value.
  change (0 <= pair_value (original_fifth_fold_d rho) / 18446744073709551616 < 1125899906842624).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma fifth_r2_value rho : field_input_bounds rho -> Int64.unsigned (original_fifth_r2 rho) = fifth_integer_c rho mod 4503599627370496.
Proof.
  intro HB; unfold original_fifth_r2, fifth_r2_machine; rewrite machine_mask52_value.
  change (Int64.unsigned (fst (original_fifth_fold_c rho)) mod 4503599627370496 = fifth_integer_c rho mod 4503599627370496).
  rewrite pair_low_mod52, fifth_fold_c_value by exact HB; reflexivity.
Qed.
Lemma fifth_r2_bound rho : 0 <= Int64.unsigned (original_fifth_r2 rho) < 4503599627370496.
Proof. unfold original_fifth_r2, fifth_r2_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia. Qed.

Local Opaque xstmt prefix_initial through_fifth original_fifth_checkpoint.
Theorem exec_original_fifth_integer_checkpoint rho beta e le m :
  field_input_bounds rho -> rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m through_fifth E0 le' mf Out_normal /\
    rep rho beta (sregs (original_fifth_checkpoint rho)) mf /\
    tmatch rho beta (stemps (original_fifth_checkpoint rho)) le' /\
    Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 0) = Some (Vlong (original_third_r0 rho)) /\
    Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8) = Some (Vlong (original_fourth_r1 rho)) /\
    Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 16) = Some (Vlong (original_fifth_r2 rho)) /\
    pair_value (original_fifth_final_c rho) = fifth_integer_c rho / 4503599627370496 /\
    pair_value (original_fifth_final_d rho) = fifth_integer_d rho / Int64.modulus /\
    Int64.unsigned (original_fifth_r2 rho) = fifth_integer_c rho mod 4503599627370496 /\
    0 <= pair_value (original_fifth_final_c rho) < 9223372036854775808 /\
    0 <= pair_value (original_fifth_final_d rho) < 1125899906842624 /\
    0 <= Int64.unsigned (original_fifth_r2 rho) < 4503599627370496 /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  intros HB HR HT HE.
  destruct (exec_original_through_fifth rho beta e le m HR HT HE) as (le' & mf & HX & HRep & HTm & H0 & H1 & H2 & HF).
  exists le', mf; split; [exact HX|]; split; [exact HRep|]; split; [exact HTm|]; split; [exact H0|]; split; [exact H1|]; split; [exact H2|];
    split; [apply fifth_final_c_value; exact HB|]; split; [apply fifth_final_d_value; exact HB|];
    split; [apply fifth_r2_value; exact HB|]; split; [apply fifth_final_c_bound; exact HB|];
    split; [apply fifth_final_d_bound; exact HB|]; split; [apply fifth_r2_bound|exact HF].
Qed.

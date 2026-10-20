(** Exact integer bridge through the original r[1] store and following shift. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events Values.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage.
Require Import C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_checkpoint_bridge C.jet_secp_multiply_checkpoint_prefix.
Require Import C.jet_secp_multiply_first_arithmetic C.jet_secp_multiply_secondvalues_accum C.jet_secp_multiply_secondvalues_arithmetic C.jet_secp_multiply_third_arithmetic.
Require Import C.jet_secp_multiply_fourth_state C.jet_secp_multiply_fourth_values C.jet_secp_multiply_fourth_execute.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fourth_pairs_c (rho : nat -> int64) := [(rho 0%nat, rho 6%nat); (rho 1%nat, rho 5%nat)].
Definition fourth_pairs_d (rho : nat -> int64) := [(rho 2%nat, rho 9%nat); (rho 3%nat, rho 8%nat); (rho 4%nat, rho 7%nat)].
Definition column1 rho := products (fourth_pairs_c rho).
Definition column6 rho := products (fourth_pairs_d rho).
Definition fourth_integer_d rho := third_integer_d rho / 4503599627370496 + column6 rho.
Definition fourth_integer_base_c rho := third_integer_c rho / 4503599627370496 + column1 rho.
Definition fourth_integer_c rho := fourth_integer_base_c rho + (fourth_integer_d rho mod 4503599627370496) * 68719492368.
Definition original_fourth_base_c rho := fourth_base_c_machine rho (original_third_final_c rho).
Definition original_fourth_fold_d rho := fourth_fold_d_machine rho (original_third_final_d rho).
Definition original_fourth_before rho := fourth_before_machine rho (original_third_final_d rho).
Definition original_fourth_fold_c rho := fourth_fold_c_machine rho (original_third_final_c rho) (original_third_final_d rho).
Definition original_fourth_final_c rho := fourth_final_c_machine rho (original_third_final_c rho) (original_third_final_d rho).
Definition original_fourth_final_d rho := fourth_final_d_machine rho (original_third_final_d rho).
Definition original_fourth_r1 rho := fourth_r1_machine rho (original_third_final_c rho) (original_third_final_d rho).

Lemma fourth_pairs_c56 rho : field_input_bounds rho -> Forall pair56 (fourth_pairs_c rho).
Proof. intro HB; unfold fourth_pairs_c; repeat constructor. all: cbn [fst snd]; apply (every_input56 rho HB); lia. Qed.
Lemma fourth_pairs_d56 rho : field_input_bounds rho -> Forall pair56 (fourth_pairs_d rho).
Proof. intro HB; unfold fourth_pairs_d; repeat constructor. all: cbn [fst snd]; apply (every_input56 rho HB); lia. Qed.
Lemma column1_bound rho : field_input_bounds rho -> 0 <= column1 rho <= 10384593717069655257060992658440192.
Proof. intro HB; exact (products56_bound (fourth_pairs_c rho) (fourth_pairs_c56 rho HB)). Qed.
Lemma column6_bound rho : field_input_bounds rho -> 0 <= column6 rho <= 15576890575604482885591488987660288.
Proof. intro HB; exact (products56_bound (fourth_pairs_d rho) (fourth_pairs_d56 rho HB)). Qed.

Local Opaque machine_accum.
Lemma fourth_c_as_accumulate rho c : fourth_base_c_machine rho c = accumulate c (fourth_pairs_c rho).
Proof. reflexivity. Qed.
Lemma fourth_d_as_accumulate rho d : fourth_fold_d_machine rho d = accumulate d (fourth_pairs_d rho).
Proof. reflexivity. Qed.
Lemma fourth_base_c_value rho : field_input_bounds rho -> pair_value (original_fourth_base_c rho) = fourth_integer_base_c rho.
Proof.
  intro HB; unfold original_fourth_base_c; rewrite fourth_c_as_accumulate, accumulate_exact.
  - unfold fourth_integer_base_c; rewrite third_final_c_value by exact HB; reflexivity.
  - pose proof (third_final_c_bound rho HB); pose proof (column1_bound rho HB).
    change (pair_value (original_third_final_c rho) + column1 rho < 340282366920938463463374607431768211456); lia.
Qed.
Lemma fourth_base_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fourth_base_c rho) < 20769187434139310514121985316880384.
Proof.
  intro HB; rewrite fourth_base_c_value by exact HB; unfold fourth_integer_base_c.
  rewrite <- third_final_c_value by exact HB; pose proof (third_final_c_bound rho HB); pose proof (column1_bound rho HB); lia.
Qed.
Lemma fourth_fold_d_value rho : field_input_bounds rho -> pair_value (original_fourth_fold_d rho) = fourth_integer_d rho.
Proof.
  intro HB; unfold original_fourth_fold_d; rewrite fourth_d_as_accumulate, accumulate_exact.
  - unfold fourth_integer_d; rewrite third_final_d_value by exact HB; reflexivity.
  - pose proof (third_final_d_bound rho HB); pose proof (column6_bound rho HB).
    change (pair_value (original_third_final_d rho) + column6 rho < 340282366920938463463374607431768211456); lia.
Qed.
Lemma fourth_fold_d_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fourth_fold_d rho) < 20769187434139310514121985316880384.
Proof.
  intro HB; rewrite fourth_fold_d_value by exact HB; unfold fourth_integer_d.
  rewrite <- third_final_d_value by exact HB; pose proof (third_final_d_bound rho HB); pose proof (column6_bound rho HB); lia.
Qed.
Lemma fourth_before_value rho : field_input_bounds rho -> Int64.unsigned (original_fourth_before rho) = fourth_integer_d rho mod 4503599627370496.
Proof.
  intro HB; unfold original_fourth_before, fourth_before_machine; rewrite machine_mask52_value.
  change (Int64.unsigned (fst (original_fourth_fold_d rho)) mod 4503599627370496 = fourth_integer_d rho mod 4503599627370496).
  rewrite pair_low_mod52, fourth_fold_d_value by exact HB; reflexivity.
Qed.
Lemma fourth_before_bound rho : 0 <= Int64.unsigned (original_fourth_before rho) < 4503599627370496.
Proof. unfold original_fourth_before, fourth_before_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia. Qed.
Lemma fourth_fold_c_value rho : field_input_bounds rho -> pair_value (original_fourth_fold_c rho) = fourth_integer_c rho.
Proof.
  intro HB; unfold original_fourth_fold_c, fourth_fold_c_machine; rewrite machine_accum_exact.
  - change (pair_value (original_fourth_base_c rho) + Int64.unsigned (original_fourth_before rho) * 68719492368 = fourth_integer_c rho).
    rewrite fourth_base_c_value, fourth_before_value by exact HB; reflexivity.
  - change (pair_value (original_fourth_base_c rho) + Int64.unsigned (original_fourth_before rho) * 68719492368 < 340282366920938463463374607431768211456).
    pose proof (fourth_base_c_bound rho HB); pose proof (fourth_before_bound rho); lia.
Qed.
Lemma fourth_fold_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fourth_fold_c rho) < 41538374868278621028243970633760768.
Proof.
  intro HB; rewrite fourth_fold_c_value by exact HB; unfold fourth_integer_c.
  rewrite <- fourth_base_c_value, <- fourth_before_value by exact HB.
  pose proof (fourth_base_c_bound rho HB); pose proof (fourth_before_bound rho); lia.
Qed.
Lemma fourth_final_c_value rho : field_input_bounds rho -> pair_value (original_fourth_final_c rho) = fourth_integer_c rho / 4503599627370496.
Proof.
  intro HB; unfold original_fourth_final_c, fourth_final_c_machine; rewrite machine_shift52_value.
  change (pair_value (original_fourth_fold_c rho) / 4503599627370496 = fourth_integer_c rho / 4503599627370496).
  rewrite fourth_fold_c_value by exact HB; reflexivity.
Qed.
Lemma fourth_final_d_value rho : field_input_bounds rho -> pair_value (original_fourth_final_d rho) = fourth_integer_d rho / 4503599627370496.
Proof.
  intro HB; unfold original_fourth_final_d, fourth_final_d_machine; rewrite machine_shift52_value.
  change (pair_value (original_fourth_fold_d rho) / 4503599627370496 = fourth_integer_d rho / 4503599627370496).
  rewrite fourth_fold_d_value by exact HB; reflexivity.
Qed.
Lemma fourth_final_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fourth_final_c rho) < 9223372036854775808.
Proof.
  intro HB; pose proof (fourth_fold_c_bound rho HB).
  unfold original_fourth_final_c, fourth_final_c_machine; rewrite machine_shift52_value.
  change (0 <= pair_value (original_fourth_fold_c rho) / 4503599627370496 < 9223372036854775808).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma fourth_final_d_bound rho : field_input_bounds rho -> 0 <= pair_value (original_fourth_final_d rho) < 4611686018427387904.
Proof.
  intro HB; pose proof (fourth_fold_d_bound rho HB).
  unfold original_fourth_final_d, fourth_final_d_machine; rewrite machine_shift52_value.
  change (0 <= pair_value (original_fourth_fold_d rho) / 4503599627370496 < 4611686018427387904).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma fourth_r1_value rho : field_input_bounds rho -> Int64.unsigned (original_fourth_r1 rho) = fourth_integer_c rho mod 4503599627370496.
Proof.
  intro HB; unfold original_fourth_r1, fourth_r1_machine; rewrite machine_mask52_value.
  change (Int64.unsigned (fst (original_fourth_fold_c rho)) mod 4503599627370496 = fourth_integer_c rho mod 4503599627370496).
  rewrite pair_low_mod52, fourth_fold_c_value by exact HB; reflexivity.
Qed.
Lemma fourth_r1_bound rho : 0 <= Int64.unsigned (original_fourth_r1 rho) < 4503599627370496.
Proof. unfold original_fourth_r1, fourth_r1_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia. Qed.

Local Opaque xstmt prefix_initial through_fourth original_fourth_checkpoint.
Theorem exec_original_fourth_integer_checkpoint rho beta e le m :
  field_input_bounds rho -> rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m through_fourth E0 le' mf Out_normal /\
    rep rho beta (sregs (original_fourth_checkpoint rho)) mf /\
    tmatch rho beta (stemps (original_fourth_checkpoint rho)) le' /\
    Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 0) = Some (Vlong (original_third_r0 rho)) /\
    Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8) = Some (Vlong (original_fourth_r1 rho)) /\
    pair_value (original_fourth_final_c rho) = fourth_integer_c rho / 4503599627370496 /\
    pair_value (original_fourth_final_d rho) = fourth_integer_d rho / 4503599627370496 /\
    Int64.unsigned (original_fourth_r1 rho) = fourth_integer_c rho mod 4503599627370496 /\
    0 <= pair_value (original_fourth_final_c rho) < 9223372036854775808 /\
    0 <= pair_value (original_fourth_final_d rho) < 4611686018427387904 /\
    0 <= Int64.unsigned (original_fourth_r1 rho) < 4503599627370496 /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  intros HB HR HT HE.
  destruct (exec_original_through_fourth rho beta e le m HR HT HE) as (le' & mf & HX & HRep & HTm & H0 & H1 & HF).
  exists le', mf; split; [exact HX|]; split; [exact HRep|]; split; [exact HTm|]; split; [exact H0|]; split; [exact H1|];
    split; [apply fourth_final_c_value; exact HB|]; split; [apply fourth_final_d_value; exact HB|];
    split; [apply fourth_r1_value; exact HB|]; split; [apply fourth_final_c_bound; exact HB|];
    split; [apply fourth_final_d_bound; exact HB|]; split; [apply fourth_r1_bound|exact HF].
Qed.

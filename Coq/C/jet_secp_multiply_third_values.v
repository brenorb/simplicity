(** Compact machine values for the third original multiplication slice. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr.
Require Import C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_checkpoint_ops.
Require Import C.jet_secp_multiply_third_state.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition third_fold_d_machine (digits : nat -> int64) (d : int64 * int64) :=
  machine_accum (machine_accum (machine_accum (machine_accum d
    (digits 1%nat) (digits 9%nat)) (digits 2%nat) (digits 8%nat))
    (digits 3%nat) (digits 7%nat)) (digits 4%nat) (digits 6%nat).
Definition third_final_d_machine digits d := machine_shift52 (third_fold_d_machine digits d).
Definition third_before_machine digits d := Int64.and (fst (third_fold_d_machine digits d)) (Int64.repr 4503599627370495).
Definition third_u0_machine digits d tx := Int64.or (Int64.shl (third_before_machine digits d) (Int64.repr 4)) tx.
Definition third_fold_c_machine (digits : nat -> int64) d tx :=
  machine_accum (machine_product (digits 0%nat) (digits 5%nat)) (third_u0_machine digits d tx)
    (Int64.shru (Int64.repr 68719492368) (Int64.repr 4)).
Definition third_final_c_machine digits d tx := machine_shift52 (third_fold_c_machine digits d tx).
Definition third_r0_machine digits d tx := Int64.and (fst (third_fold_c_machine digits d tx)) (Int64.repr 4503599627370495).

Lemma third_fold_d_den rho beta digits d : pair_den rho beta (third_fold_d_sy digits d) = third_fold_d_machine digits d.
Proof. unfold third_fold_d_sy, third_fold_d_machine; rewrite !sx_accum_machine; reflexivity. Qed.
Lemma third_final_d_den rho beta digits d : pair_den rho beta (third_final_d_sy digits d) = third_final_d_machine digits d.
Proof. unfold third_final_d_sy, third_final_d_machine; rewrite sx_shift52_machine, third_fold_d_den; reflexivity. Qed.
Lemma third_before_den rho beta digits d : den rho beta (third_before_sy digits d) = Vlong (third_before_machine digits d).
Proof.
  unfold third_before_sy, third_before_machine.
  change (Vlong (Int64.and (fst (pair_den rho beta (third_fold_d_sy digits d))) (Int64.repr 4503599627370495)) =
    Vlong (Int64.and (fst (third_fold_d_machine digits d)) (Int64.repr 4503599627370495))).
  rewrite third_fold_d_den; reflexivity.
Qed.
Lemma third_u0_den rho beta digits d tx : den rho beta (third_u0_sy digits d tx) = Vlong (third_u0_machine digits d tx).
Proof.
  unfold third_u0_sy, third_u0_machine.
  change (Vlong (Int64.or (Int64.shl (il (den rho beta (third_before_sy digits d))) (Int64.repr 4)) tx) =
    Vlong (Int64.or (Int64.shl (third_before_machine digits d) (Int64.repr 4)) tx)).
  rewrite third_before_den; reflexivity.
Qed.
Lemma third_fold_c_den rho beta digits d tx : pair_den rho beta (third_fold_c_sy digits d tx) = third_fold_c_machine digits d tx.
Proof.
  unfold third_fold_c_sy, third_fold_c_machine; rewrite sx_accum_machine, sx_product_machine.
  unfold word_den; rewrite third_u0_den; reflexivity.
Qed.
Lemma third_final_c_den rho beta digits d tx : pair_den rho beta (third_final_c_sy digits d tx) = third_final_c_machine digits d tx.
Proof. unfold third_final_c_sy, third_final_c_machine; rewrite sx_shift52_machine, third_fold_c_den; reflexivity. Qed.
Lemma third_r0_den rho beta digits d tx : den rho beta (third_r0_sy digits d tx) = Vlong (third_r0_machine digits d tx).
Proof.
  unfold third_r0_sy, third_r0_machine.
  change (Vlong (Int64.and (fst (pair_den rho beta (third_fold_c_sy digits d tx))) (Int64.repr 4503599627370495)) =
    Vlong (Int64.and (fst (third_fold_c_machine digits d tx)) (Int64.repr 4503599627370495))).
  rewrite third_fold_c_den; reflexivity.
Qed.

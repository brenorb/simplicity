(** Third original C checkpoint: derive carries and r[0] from input bounds. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage.
Require Import C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_checkpoint_bridge C.jet_secp_multiply_checkpoint_prefix C.jet_secp_multiply_checkpoint_atomic.
Require Import C.jet_secp_multiply_first_arithmetic C.jet_secp_multiply_secondvalues_accum C.jet_secp_multiply_secondvalues_arithmetic.
Require Import C.jet_secp_multiply_third_state C.jet_secp_multiply_third_values C.jet_secp_multiply_third_machine C.jet_secp_multiply_third_compose.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition third_pairs (rho : nat -> int64) :=
  [(rho 1%nat, rho 9%nat); (rho 2%nat, rho 8%nat); (rho 3%nat, rho 7%nat); (rho 4%nat, rho 6%nat)].
Definition column5 rho := products (third_pairs rho).
Definition third_integer_d rho := second_integer_fold rho / 4503599627370496 + column5 rho.
Definition third_integer_u0 rho := (third_integer_d rho mod 4503599627370496) * 16 +
  (second_integer_fold rho mod 4503599627370496) / 281474976710656.
Definition third_integer_c rho := Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 5%nat) + third_integer_u0 rho * 4294968273.
Definition original_third_fold_d rho := third_fold_d_machine rho (original_second_final rho).
Definition original_third_final_d rho := third_final_d_machine rho (original_second_final rho).
Definition original_third_before rho := third_before_machine rho (original_second_final rho).
Definition original_third_u0 rho := third_u0_machine rho (original_second_final rho) (original_second_tx rho).
Definition original_third_fold_c rho := third_fold_c_machine rho (original_second_final rho) (original_second_tx rho).
Definition original_third_final_c rho := third_final_c_machine rho (original_second_final rho) (original_second_tx rho).
Definition original_third_r0 rho := third_r0_machine rho (original_second_final rho) (original_second_tx rho).

Lemma third_pairs56 rho : field_input_bounds rho -> Forall pair56 (third_pairs rho).
Proof.
  intro HB; unfold third_pairs; repeat constructor.
  all: cbn [fst snd]; apply (every_input56 rho HB); lia.
Qed.
Lemma column5_bound rho : field_input_bounds rho -> 0 <= column5 rho <= 20769187434139310514121985316880384.
Proof. intro HB; exact (products56_bound (third_pairs rho) (third_pairs56 rho HB)). Qed.

Local Opaque machine_accum.
Lemma third_as_accumulate rho d : third_fold_d_machine rho d = accumulate d (third_pairs rho).
Proof. reflexivity. Qed.
Lemma third_fold_d_value rho : field_input_bounds rho -> pair_value (original_third_fold_d rho) = third_integer_d rho.
Proof.
  intro HB; unfold original_third_fold_d; rewrite third_as_accumulate, accumulate_exact.
  - unfold third_integer_d; rewrite second_final_value by exact HB; reflexivity.
  - pose proof (second_final_bound rho HB); pose proof (column5_bound rho HB).
    change (Int64.modulus * Int64.modulus) with 340282366920938463463374607431768211456.
    change (pair_value (original_second_final rho) + column5 rho < 340282366920938463463374607431768211456); lia.
Qed.
Lemma third_fold_d_bound rho : field_input_bounds rho -> 0 <= pair_value (original_third_fold_d rho) < 41538374868278621028243970633760768.
Proof.
  intro HB; rewrite third_fold_d_value by exact HB; unfold third_integer_d.
  rewrite <- second_final_value by exact HB.
  pose proof (second_final_bound rho HB); pose proof (column5_bound rho HB); lia.
Qed.
Lemma third_final_d_value rho : field_input_bounds rho -> pair_value (original_third_final_d rho) = third_integer_d rho / 4503599627370496.
Proof.
  intro HB; unfold original_third_final_d, third_final_d_machine; rewrite machine_shift52_value.
  change (pair_value (original_third_fold_d rho) / 4503599627370496 = third_integer_d rho / 4503599627370496).
  rewrite third_fold_d_value by exact HB; reflexivity.
Qed.
Lemma third_final_d_bound rho : field_input_bounds rho -> 0 <= pair_value (original_third_final_d rho) < 9223372036854775808.
Proof.
  intro HB; pose proof (third_fold_d_bound rho HB).
  unfold original_third_final_d, third_final_d_machine; rewrite machine_shift52_value.
  change (0 <= pair_value (original_third_fold_d rho) / 4503599627370496 < 9223372036854775808).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma third_before_value rho : field_input_bounds rho -> Int64.unsigned (original_third_before rho) = third_integer_d rho mod 4503599627370496.
Proof.
  intro HB; unfold original_third_before, third_before_machine; rewrite machine_mask52_value.
  change (Int64.unsigned (fst (original_third_fold_d rho)) mod 4503599627370496 = third_integer_d rho mod 4503599627370496).
  rewrite pair_low_mod52, third_fold_d_value by exact HB; reflexivity.
Qed.
Lemma third_before_bound rho : 0 <= Int64.unsigned (original_third_before rho) < 4503599627370496.
Proof.
  unfold original_third_before, third_before_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia.
Qed.
Lemma shl4_or_unsigned x y : Int64.unsigned x < 4503599627370496 -> Int64.unsigned y < 16 ->
  Int64.unsigned (Int64.or (Int64.shl x (Int64.repr 4)) y) = Int64.unsigned x * 16 + Int64.unsigned y.
Proof.
  intros HX HY; rewrite Int64.shifted_or_is_add.
  - change (Int64.unsigned (Int64.repr (Int64.unsigned x * 16 + Int64.unsigned y)) = Int64.unsigned x * 16 + Int64.unsigned y).
    apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615.
    pose proof (Int64.unsigned_range x); pose proof (Int64.unsigned_range y); lia.
  - change (0 <= 4 < 64); lia.
  - exact HY.
Qed.
Lemma third_u0_value rho : field_input_bounds rho -> Int64.unsigned (original_third_u0 rho) = third_integer_u0 rho.
Proof.
  intro HB; unfold original_third_u0, third_u0_machine.
  rewrite shl4_or_unsigned; [|apply third_before_bound|exact (proj2 (second_tx_bound rho HB))].
  change (Int64.unsigned (original_third_before rho) * 16 + Int64.unsigned (original_second_tx rho) = third_integer_u0 rho).
  unfold third_integer_u0; rewrite third_before_value, second_tx_value by exact HB; reflexivity.
Qed.
Lemma third_u0_bound rho : field_input_bounds rho -> 0 <= Int64.unsigned (original_third_u0 rho) < 72057594037927936.
Proof.
  intro HB; unfold original_third_u0, third_u0_machine.
  rewrite shl4_or_unsigned; [|apply third_before_bound|exact (proj2 (second_tx_bound rho HB))].
  change (0 <= Int64.unsigned (original_third_before rho) * 16 + Int64.unsigned (original_second_tx rho) < 72057594037927936).
  pose proof (third_before_bound rho); pose proof (second_tx_bound rho HB); lia.
Qed.
Lemma low_reduction_unsigned : Int64.unsigned (Int64.shru (Int64.repr 68719492368) (Int64.repr 4)) = 4294968273.
Proof. vm_compute; reflexivity. Qed.
Lemma third_fold_c_value rho : field_input_bounds rho -> pair_value (original_third_fold_c rho) = third_integer_c rho.
Proof.
  intro HB; unfold original_third_fold_c, third_fold_c_machine; rewrite machine_accum_exact.
  - rewrite machine_product_value, low_reduction_unsigned.
    change (Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 5%nat) + Int64.unsigned (original_third_u0 rho) * 4294968273 = third_integer_c rho).
    rewrite third_u0_value by exact HB; reflexivity.
  - rewrite machine_product_value, low_reduction_unsigned.
    change (Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 5%nat) + Int64.unsigned (original_third_u0 rho) * 4294968273 < Int64.modulus * Int64.modulus).
    pose proof (third_u0_bound rho HB).
    pose proof (product56_range (rho 0%nat) (rho 5%nat) (every_input56 rho HB 0%nat ltac:(lia)) (every_input56 rho HB 5%nat ltac:(lia))).
    change (Int64.modulus * Int64.modulus) with 340282366920938463463374607431768211456; lia.
Qed.
Lemma third_fold_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_third_fold_c rho) < 10384593717069655257060992658440192.
Proof.
  intro HB; rewrite third_fold_c_value by exact HB; unfold third_integer_c.
  rewrite <- third_u0_value by exact HB; pose proof (third_u0_bound rho HB).
  pose proof (product56_range (rho 0%nat) (rho 5%nat) (every_input56 rho HB 0%nat ltac:(lia)) (every_input56 rho HB 5%nat ltac:(lia))); lia.
Qed.
Lemma third_final_c_value rho : field_input_bounds rho -> pair_value (original_third_final_c rho) = third_integer_c rho / 4503599627370496.
Proof.
  intro HB; unfold original_third_final_c, third_final_c_machine; rewrite machine_shift52_value.
  change (pair_value (original_third_fold_c rho) / 4503599627370496 = third_integer_c rho / 4503599627370496).
  rewrite third_fold_c_value by exact HB; reflexivity.
Qed.
Lemma third_final_c_bound rho : field_input_bounds rho -> 0 <= pair_value (original_third_final_c rho) < 2305843009213693952.
Proof.
  intro HB; pose proof (third_fold_c_bound rho HB).
  unfold original_third_final_c, third_final_c_machine; rewrite machine_shift52_value.
  change (0 <= pair_value (original_third_fold_c rho) / 4503599627370496 < 2305843009213693952).
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.
Lemma third_r0_value rho : field_input_bounds rho -> Int64.unsigned (original_third_r0 rho) = third_integer_c rho mod 4503599627370496.
Proof.
  intro HB; unfold original_third_r0, third_r0_machine; rewrite machine_mask52_value.
  change (Int64.unsigned (fst (original_third_fold_c rho)) mod 4503599627370496 = third_integer_c rho mod 4503599627370496).
  rewrite pair_low_mod52, third_fold_c_value by exact HB; reflexivity.
Qed.
Lemma third_r0_bound rho : 0 <= Int64.unsigned (original_third_r0 rho) < 4503599627370496.
Proof. unfold original_third_r0, third_r0_machine; rewrite machine_mask52_value; apply Z.mod_pos_bound; lia. Qed.

Local Opaque xstmt prefix_initial composed_third_state through_third.
Theorem exec_original_third_integer_atomic rho beta e le m :
  field_input_bounds rho ->
  rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m through_third E0 le' mf Out_normal /\
    composed_third_observations rho beta le' mf /\
    pair_value (original_third_final_d rho) = third_integer_d rho / 4503599627370496 /\
    pair_value (original_third_final_c rho) = third_integer_c rho / 4503599627370496 /\
    Int64.unsigned (original_third_r0 rho) = third_integer_c rho mod 4503599627370496 /\
    Int64.unsigned (original_third_u0 rho) = third_integer_u0 rho /\
    0 <= pair_value (original_third_final_d rho) < 9223372036854775808 /\
    0 <= pair_value (original_third_final_c rho) < 2305843009213693952 /\
    0 <= Int64.unsigned (original_third_r0 rho) < 4503599627370496 /\
    0 <= Int64.unsigned (original_third_u0 rho) < 72057594037927936 /\
    rep rho beta (sregs (atomic_state rho beta (composed_third_state rho))) mf /\
    tmatch rho beta (stemps (atomic_state rho beta (composed_third_state rho))) le' /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  intros HB HR HT HE.
  destruct (exec_original_through_third rho beta e le m HR HT HE) as (le' & mf & HX & HM & HRep & HTm & HF).
  exists le', mf; split; [exact HX|]; split; [exact HM|];
    split; [apply third_final_d_value; exact HB|]; split; [apply third_final_c_value; exact HB|];
    split; [apply third_r0_value; exact HB|]; split; [apply third_u0_value; exact HB|];
    split; [apply third_final_d_bound; exact HB|]; split; [apply third_final_c_bound; exact HB|];
    split; [apply third_r0_bound|]; split; [apply third_u0_bound; exact HB|];
    split; [exact HRep|]; split; assumption.
Qed.

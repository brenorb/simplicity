(** Full product reconstruction of the checked machine schedule. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_scalar_mul512_machine C.jet_secp_scalar_mul512_columns
  C.jet_secp_scalar_mul512_accumulate C.jet_secp_scalar_mul512_low.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition mul512_c0 (rho : nat -> int64) := column_muladd_fast (rho 0%nat) (rho 4%nat) column_zero.
Definition mul512_ps1 (rho : nat -> int64) := [(rho 0%nat,rho 5%nat); (rho 1%nat,rho 4%nat)].
Definition mul512_ps2 (rho : nat -> int64) := [(rho 0%nat,rho 6%nat); (rho 1%nat,rho 5%nat); (rho 2%nat,rho 4%nat)].
Definition mul512_ps3 (rho : nat -> int64) := [(rho 0%nat,rho 7%nat); (rho 1%nat,rho 6%nat); (rho 2%nat,rho 5%nat); (rho 3%nat,rho 4%nat)].
Definition mul512_ps4 (rho : nat -> int64) := [(rho 1%nat,rho 7%nat); (rho 2%nat,rho 6%nat); (rho 3%nat,rho 5%nat)].
Definition mul512_ps5 (rho : nat -> int64) := [(rho 2%nat,rho 7%nat); (rho 3%nat,rho 6%nat)].
Definition mul512_c1 rho := column_accumulate (mul512_ps1 rho) (column_extract_fast (mul512_c0 rho)).
Definition mul512_c2 rho := column_accumulate (mul512_ps2 rho) (column_extract (mul512_c1 rho)).
Definition mul512_c3 rho := column_accumulate (mul512_ps3 rho) (column_extract (mul512_c2 rho)).
Definition mul512_c4 rho := column_accumulate (mul512_ps4 rho) (column_extract (mul512_c3 rho)).
Definition mul512_c5 rho := column_accumulate (mul512_ps5 rho) (column_extract (mul512_c4 rho)).
Definition mul512_c6 rho := column_muladd_fast (rho 3%nat) (rho 7%nat) (column_extract (mul512_c5 rho)).
Definition mul512_prefix rho := [col_lo (mul512_c0 rho); col_lo (mul512_c1 rho);
  col_lo (mul512_c2 rho); col_lo (mul512_c3 rho); col_lo (mul512_c4 rho); col_lo (mul512_c5 rho)].
Definition mul512_residual rho := column_value (column_extract (mul512_c5 rho)) +
  Int64.unsigned (rho 3%nat) * Int64.unsigned (rho 7%nat).

Lemma mul512_schedule rho : scalar_mul512_machine_outputs rho =
  mul512_prefix rho ++ [col_lo (mul512_c6 rho); col_hi (mul512_c6 rho)].
Proof. reflexivity. Qed.

Lemma mul512_column_values rho :
  column_value (mul512_c1 rho) = column_value (column_extract_fast (mul512_c0 rho)) + column_products (mul512_ps1 rho) /\
  column_value (mul512_c2 rho) = column_value (column_extract (mul512_c1 rho)) + column_products (mul512_ps2 rho) /\
  column_value (mul512_c3 rho) = column_value (column_extract (mul512_c2 rho)) + column_products (mul512_ps3 rho) /\
  column_value (mul512_c4 rho) = column_value (column_extract (mul512_c3 rho)) + column_products (mul512_ps4 rho) /\
  column_value (mul512_c5 rho) = column_value (column_extract (mul512_c4 rho)) + column_products (mul512_ps5 rho).
Proof.
  pose proof (column_fast_carry_small (rho 0%nat) (rho 4%nat)) as H0.
  change (column_value (column_extract_fast (mul512_c0 rho)) < 5 * Int64.modulus) in H0.
  destruct (column_accumulate_small (mul512_ps1 rho) _ ltac:(cbn [mul512_ps1 length]; lia) H0) as [E1 [_ H1]].
  change (column_value (column_extract (mul512_c1 rho)) < 5 * Int64.modulus) in H1.
  destruct (column_accumulate_small (mul512_ps2 rho) _ ltac:(cbn [mul512_ps2 length]; lia) H1) as [E2 [_ H2]].
  change (column_value (column_extract (mul512_c2 rho)) < 5 * Int64.modulus) in H2.
  destruct (column_accumulate_small (mul512_ps3 rho) _ ltac:(cbn [mul512_ps3 length]; lia) H2) as [E3 [_ H3]].
  change (column_value (column_extract (mul512_c3 rho)) < 5 * Int64.modulus) in H3.
  destruct (column_accumulate_small (mul512_ps4 rho) _ ltac:(cbn [mul512_ps4 length]; lia) H3) as [E4 [_ H4]].
  change (column_value (column_extract (mul512_c4 rho)) < 5 * Int64.modulus) in H4.
  destruct (column_accumulate_small (mul512_ps5 rho) _ ltac:(cbn [mul512_ps5 length]; lia) H4) as [E5 [_ H5]].
  exact (conj E1 (conj E2 (conj E3 (conj E4 E5)))).
Qed.

Lemma mul512_input_bound rho start :
  0 <= scalar_mul512_input_value rho start < Int64.modulus ^ 4.
Proof.
  replace (scalar_mul512_input_value rho start) with
    (column_words_value [rho start; rho (start+1)%nat; rho (start+2)%nat; rho (start+3)%nat])
    by (unfold scalar_mul512_input_value; cbn [column_words_value]; ring).
  apply (column_words_bound [rho start; rho (start+1)%nat; rho (start+2)%nat; rho (start+3)%nat]).
Qed.
Lemma mul512_product_bound rho :
  0 <= scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4 < Int64.modulus ^ 8.
Proof.
  pose proof (mul512_input_bound rho 0); pose proof (mul512_input_bound rho 4).
  replace (Int64.modulus ^ 8) with (Int64.modulus ^ 4 * Int64.modulus ^ 4) by (rewrite <- Z.pow_add_r by lia; reflexivity).
  nia.
Qed.

Lemma mul512_reconstruction rho :
  scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4 =
    column_words_value (mul512_prefix rho) + Int64.modulus ^ 6 * mul512_residual rho.
Proof.
  destruct (mul512_column_values rho) as [E1 [E2 [E3 [E4 E5]]]].
  pose proof (column_fast_zero_product (rho 0%nat) (rho 4%nat)) as E0.
  change (column_value (mul512_c0 rho) = Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 4%nat)) in E0.
  pose proof (column_fast_extract_decomposition (mul512_c0 rho) eq_refl) as D0.
  pose proof (column_extract_decomposition (mul512_c1 rho)) as D1.
  pose proof (column_extract_decomposition (mul512_c2 rho)) as D2.
  pose proof (column_extract_decomposition (mul512_c3 rho)) as D3.
  pose proof (column_extract_decomposition (mul512_c4 rho)) as D4.
  pose proof (column_extract_decomposition (mul512_c5 rho)) as D5.
  cbn [mul512_ps1 mul512_ps2 mul512_ps3 mul512_ps4 mul512_ps5 column_products] in E1,E2,E3,E4,E5.
  unfold scalar_mul512_input_value,mul512_prefix,mul512_residual; cbn [Nat.add column_words_value].
  change Int64.modulus with 18446744073709551616 in *.
  cbn [Z.pow]; nia.
Qed.

Lemma mul512_residual_bound rho : 0 <= mul512_residual rho < Int64.modulus * Int64.modulus.
Proof.
  pose proof (mul512_reconstruction rho) as HE.
  pose proof (mul512_product_bound rho) as HP.
  pose proof (column_words_bound (mul512_prefix rho)) as HW.
  pose proof (column_value_nonnegative (column_extract (mul512_c5 rho))) as HC.
  pose proof (Int64.unsigned_range (rho 3%nat)); pose proof (Int64.unsigned_range (rho 7%nat)).
  unfold mul512_residual in *.
  change Int64.modulus with 18446744073709551616 in *.
  cbn [Z.pow] in *; nia.
Qed.

Lemma mul512_final_column rho : column_value (mul512_c6 rho) = mul512_residual rho.
Proof.
  unfold mul512_c6,mul512_residual.
  apply column_fast_value; [reflexivity|exact (proj2 (mul512_residual_bound rho))].
Qed.
Theorem scalar_mul512_machine_product rho :
  column_words_value (scalar_mul512_machine_outputs rho) =
    scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4.
Proof.
  rewrite mul512_schedule,column_words_append.
  rewrite mul512_reconstruction.
  change (column_words_value (mul512_prefix rho) + Int64.modulus ^ 6 *
    (Int64.unsigned (col_lo (mul512_c6 rho)) + Int64.modulus * (Int64.unsigned (col_hi (mul512_c6 rho)) + Int64.modulus * 0)) =
    column_words_value (mul512_prefix rho) + Int64.modulus ^ 6 * mul512_residual rho).
  assert (H : Int64.unsigned (col_lo (mul512_c6 rho)) + Int64.modulus *
    (Int64.unsigned (col_hi (mul512_c6 rho)) + Int64.modulus * 0) = column_value (mul512_c6 rho)).
  { unfold column_value; change (Int.unsigned (col_top (mul512_c6 rho))) with 0; reflexivity. }
  rewrite H,mul512_final_column; reflexivity.
Qed.

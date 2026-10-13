(** Exact integer interpretation of the original final carry/overflow reduction. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import C.jet_sx_zval C.jet_secp_canonical_scalar C.jet_secp_scalar_overflow_numeric
  C.jet_secp_scalar_overflow_flags C.jet_secp_scalar_reduce_numeric.
Require Import C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_fold_bounds.
Require Import C.jet_secp_reduce512_first_value.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section TYPED.
Variable digits : nat -> int64.
Variable carry : int64.
Definition final_untruncated := scalar_limb_value digits + reduce512_radix * Int64.unsigned carry.
Definition final_flag_bool := Z.eqb (final_flag_integer digits carry) 1.
Lemma final_carry_one_no_overflow : Int64.unsigned carry = 1 ->
  final_untruncated < 2 * canonical_group_order -> scalar_overflow_bool digits = false.
Proof.
  intros HC HB; unfold final_untruncated in HB; rewrite HC in HB.
  pose proof reduce512_delta_order as HD; destruct reduce512_delta_bounds as [HR _].
  rewrite scalar_overflow_matches_bound; apply Z.leb_gt; lia.
Qed.
Lemma final_flag_bound : Int64.unsigned carry <= 1 -> final_untruncated < 2 * canonical_group_order ->
  0 <= final_flag_integer digits carry <= 1.
Proof.
  intros HC HB; pose proof (Int64.unsigned_range carry) as HR.
  assert (HCases : Int64.unsigned carry = 0 \/ Int64.unsigned carry = 1) by lia.
  destruct HCases as [HC0|HC1].
  - unfold final_flag_integer; rewrite HC0; pose proof (b2z_range (scalar_overflow_bool digits)); lia.
  - pose proof (final_carry_one_no_overflow HC1 HB) as HO.
    unfold final_flag_integer; rewrite HC1,HO; cbn [b2z]; lia.
Qed.
Lemma final_flag_bool_value : Int64.unsigned carry <= 1 -> final_untruncated < 2 * canonical_group_order ->
  final_flag_integer digits carry = b2z final_flag_bool.
Proof.
  intros HC HB; pose proof (final_flag_bound HC HB) as HF.
  unfold final_flag_bool; destruct (Z.eqb_spec (final_flag_integer digits carry) 1); cbn [b2z]; lia.
Qed.
Lemma final_modulo_identity : Int64.unsigned carry <= 1 -> final_untruncated < 2 * canonical_group_order ->
  (scalar_limb_value digits + final_flag_integer digits carry * first_delta) mod reduce512_radix =
    final_untruncated mod canonical_group_order.
Proof.
  intros HC HB; pose proof (Int64.unsigned_range carry) as HR.
  pose proof (scalar_limb_value_range digits) as HX.
  assert (RR : reduce512_radix = 2 ^ 256) by reflexivity.
  rewrite <- RR in HX.
  pose proof reduce512_delta_order as HD.
  destruct reduce512_delta_bounds as [HDpos _].
  assert (HN : 0 < canonical_group_order) by (pose proof canonical_group_order_range; lia).
  assert (Hcases : Int64.unsigned carry = 0 \/ Int64.unsigned carry = 1) by lia.
  destruct Hcases as [HC0|HC1].
  - unfold final_untruncated in *; rewrite HC0 in *; rewrite Z.mul_0_r,Z.add_0_r in *.
    unfold final_flag_integer; rewrite HC0,Z.add_0_l,scalar_overflow_matches_bound.
    destruct (Z.leb_spec0 canonical_group_order (scalar_limb_value digits)) as [HG|HL]; cbn [b2z].
    + replace (scalar_limb_value digits + 1 * first_delta) with
        ((scalar_limb_value digits - canonical_group_order) + 1 * reduce512_radix) by lia.
      replace (scalar_limb_value digits) with
        ((scalar_limb_value digits - canonical_group_order) + 1 * canonical_group_order) at 2 by ring.
      rewrite !Z.mod_add by lia; rewrite !Z.mod_small by lia; reflexivity.
    + rewrite Z.mul_0_l,Z.add_0_r,!Z.mod_small by lia; reflexivity.
  - pose proof (final_carry_one_no_overflow HC1 HB) as HO.
    unfold final_untruncated in *; rewrite HC1 in *; rewrite Z.mul_1_r in *.
    unfold final_flag_integer; rewrite HC1,HO; cbn [b2z]; rewrite Z.add_0_r,Z.mul_1_l.
    replace (scalar_limb_value digits + reduce512_radix) with
      ((scalar_limb_value digits + first_delta) + 1 * canonical_group_order) by lia.
    rewrite Z.mod_add by lia; rewrite !Z.mod_small by lia; reflexivity.
Qed.
Theorem final_suffix_numeric rho beta : Int64.unsigned carry <= 1 ->
  final_untruncated < 2 * canonical_group_order ->
  final_output_value digits carry rho beta = final_untruncated mod canonical_group_order.
Proof.
  intros HC HB.
  rewrite (final_output_weighted digits carry rho beta HC final_flag_bool (final_flag_bool_value HC HB)).
  rewrite <- (final_flag_bool_value HC HB).
  change (2 ^ 256 - canonical_group_order) with (reduce512_radix - canonical_group_order).
  rewrite <- reduce512_delta_order.
  change (2 ^ 256) with reduce512_radix.
  apply final_modulo_identity; assumption.
Qed.
End TYPED.

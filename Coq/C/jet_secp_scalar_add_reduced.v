(** Weighted value of the actual scalar-add output, reusing the proven original
    reduction expression. The final public literal program remains separate. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_sx_eval C.jet_sx_zval.
Require Import C.jet_secp_scalar_reduce_numeric C.jet_secp_scalar_overflow_numeric.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_add_exec C.jet_secp_scalar_add_values.
Require Import C.jet_secp_scalar_add_numeric C.jet_secp_scalar_add_flag.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_add_limb rho layout i :=
  il (den rho layout (nth i scalar_add_limbs (XLc Int64.zero))).
Definition scalar_add_output_value rho layout := scalar_limb_value (scalar_add_limb rho layout).

Lemma scalar_add_limb_reduced_value rho layout i : (i < 4)%nat ->
  scalar_add_limb rho layout i = scalar_reduce_limb (scalar_add_reduction_rho rho layout) layout i.
Proof.
  intro HI; unfold scalar_add_limb, scalar_reduce_limb.
  rewrite scalar_add_reduction_exact.
  destruct i as [|[|[|[|i]]]]; try lia; cbn [nth map];
    rewrite scalar_add_bound_value; reflexivity.
Qed.

Lemma scalar_add_output_weighted rho layout :
  0 <= scalar_add_input_value rho < 2 * canonical_group_order ->
  scalar_add_output_value rho layout =
    (scalar_add_raw_value rho layout +
      b2z (Z.leb canonical_group_order (scalar_add_input_value rho)) *
        (2 ^ 256 - canonical_group_order)) mod 2 ^ 256.
Proof.
  intro HS.
  unfold scalar_add_output_value, scalar_limb_value at 1.
  rewrite !scalar_add_limb_reduced_value by lia.
  fold (scalar_limb_value (scalar_reduce_limb (scalar_add_reduction_rho rho layout) layout)).
  rewrite scalar_reduce_limb_value.
  rewrite (scalar_reduce_weighted_value (scalar_add_reduction_rho rho layout) layout
    (Z.leb canonical_group_order (scalar_add_input_value rho))
    (scalar_add_reduction_flag_reduced rho layout HS)).
  rewrite scalar_add_reduction_input_value; reflexivity.
Qed.

Lemma scalar_add_modulus_bridge s :
  0 <= s < 2 * canonical_group_order ->
  (s mod 2 ^ 256 + b2z (Z.leb canonical_group_order s) *
    (2 ^ 256 - canonical_group_order)) mod 2 ^ 256 = s mod canonical_group_order.
Proof.
  intro HS.
  destruct canonical_group_order_range as [[HN HP] HNP].
  change (canonical_group_order < 2 ^ 256) in HP.
  change (2 ^ 256 < 2 * canonical_group_order) in HNP.
  destruct (Z.leb_spec0 canonical_group_order s) as [HGe|HLt]; cbn [b2z].
  - assert (HNmod : s mod canonical_group_order = s - canonical_group_order).
    { replace s with ((s - canonical_group_order) + 1 * canonical_group_order) at 1 by ring.
      rewrite Z.mod_add by lia; apply Z.mod_small; lia. }
    rewrite HNmod, Z.mul_1_l.
    destruct (Z_lt_ge_dec s (2 ^ 256)) as [HLtP|HGeP].
    + rewrite (Z.mod_small s (2 ^ 256)) by lia.
      replace (s + (2 ^ 256 - canonical_group_order)) with
        ((s - canonical_group_order) + 1 * 2 ^ 256) by ring.
      rewrite Z.mod_add by lia; apply Z.mod_small; lia.
    + assert (HPmod : s mod 2 ^ 256 = s - 2 ^ 256).
      { replace s with ((s - 2 ^ 256) + 1 * 2 ^ 256) at 1 by ring.
        rewrite Z.mod_add by lia; apply Z.mod_small; lia. }
      rewrite HPmod.
      replace (s - 2 ^ 256 + (2 ^ 256 - canonical_group_order)) with
        (s - canonical_group_order) by ring.
      apply Z.mod_small; lia.
  - rewrite Z.mul_0_l, Z.add_0_r.
    rewrite (Z.mod_small s (2 ^ 256)) by lia.
    rewrite !Z.mod_small by lia; reflexivity.
Qed.

Theorem scalar_add_output_mod_group rho layout :
  0 <= scalar_add_input_value rho < 2 * canonical_group_order ->
  scalar_add_output_value rho layout = scalar_add_input_value rho mod canonical_group_order.
Proof.
  intro HS; rewrite scalar_add_output_weighted by exact HS.
  rewrite (proj1 (scalar_add_raw_and_carry rho layout)); apply scalar_add_modulus_bridge; exact HS.
Qed.

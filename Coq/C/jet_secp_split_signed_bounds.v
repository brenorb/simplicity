(** Exact signed values behind the original split_lambda modular stores.
    The small bounds follow from the actual rounded coefficients and fixed
    constants. No lattice, inverse or small-output property is assumed. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_canonical_scalar C.jet_secp_split_multipliers
 C.jet_secp_split_constants C.jet_secp_scalar_lambda_global.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition split_lattice_b2 : Z := 0x3086d221a7d46bcde86c90e49284eb15.
Definition split_lattice_a2 : Z := 0x114ca50f7a8e2f3f657c1108d9d44cfd8.
Definition split_signed_first k := k-split_lattice_b2*split_coefficient true k-
 split_lattice_a2*split_coefficient false k.
Definition split_signed_second k := split_basis_value true*split_coefficient true k-
 split_lattice_b2*split_coefficient false k.

Lemma split_rounded_error first k :
 -2^383<2^384*split_coefficient first k-k*split_multiplier_value first<=2^383.
Proof.
 unfold split_coefficient.
 pose proof (Z.div_mod (k*split_multiplier_value first+2^383) (2^384) ltac:(lia)).
 pose proof (Z.mod_pos_bound (k*split_multiplier_value first+2^383) (2^384) ltac:(lia)).
 nia.
Qed.

Lemma split_small_from_rounding k c1 c2 : 0<=k<canonical_group_order ->
 -2^383<2^384*c1-k*split_multiplier_value true<=2^383 ->
 -2^383<2^384*c2-k*split_multiplier_value false<=2^383 ->
 (-2^128<k-split_lattice_b2*c1-split_lattice_a2*c2<2^128) /\
 (-2^128<split_basis_value true*c1-split_lattice_b2*c2<2^128).
Proof.
 intros K C1 C2.
 cbv [canonical_group_order split_lattice_b2 split_lattice_a2 split_basis_value split_multiplier_value] in *.
 split;timeout 10 lia.
Qed.
Theorem split_signed_bounds k : 0<=k<canonical_group_order ->
 (-2^128<split_signed_first k<2^128) /\ (-2^128<split_signed_second k<2^128).
Proof.
 intro K;apply split_small_from_rounding;[exact K|apply split_rounded_error|apply split_rounded_error].
Qed.

Definition split_lattice_q1 := (split_basis_value true*canonical_lambda_value-split_lattice_b2)/canonical_group_order.
Definition split_lattice_q2 := (-split_lattice_b2*canonical_lambda_value-split_lattice_a2)/canonical_group_order.
Lemma split_lattice_relations :
 split_basis_value true*canonical_lambda_value=split_lattice_b2+split_lattice_q1*canonical_group_order /\
 -split_lattice_b2*canonical_lambda_value=split_lattice_a2+split_lattice_q2*canonical_group_order.
Proof. vm_compute;split;reflexivity. Qed.
Lemma split_order_nonzero : canonical_group_order<>0.
Proof. pose proof canonical_group_order_range;lia. Qed.

Theorem split_second_signed k : split_second_value k=split_signed_second k mod canonical_group_order.
Proof.
 unfold split_second_value,split_product,split_signed_second.
 rewrite <-Z.add_mod by exact split_order_nonzero.
 assert (Basis2:split_basis_value false=canonical_group_order-split_lattice_b2) by reflexivity.
 rewrite Basis2.
 replace (split_coefficient true k*split_basis_value true+
  split_coefficient false k*(canonical_group_order-split_lattice_b2)) with
  ((split_coefficient true k*split_basis_value true-split_coefficient false k*split_lattice_b2)+
   split_coefficient false k*canonical_group_order) by ring.
 rewrite Z.mod_add by exact split_order_nonzero;f_equal;ring.
Qed.

Lemma split_negate_sum_mod x k :
 ((-(x mod canonical_group_order)) mod canonical_group_order+k) mod canonical_group_order=
 (k-x) mod canonical_group_order.
Proof.
 rewrite Z.add_mod_idemp_l by exact split_order_nonzero.
 replace (- (x mod canonical_group_order)+k) with (k-x mod canonical_group_order) by ring.
 rewrite (Zminus_mod k (x mod canonical_group_order) canonical_group_order).
 rewrite (Zminus_mod k x canonical_group_order).
 rewrite Z.mod_mod by exact split_order_nonzero;reflexivity.
Qed.
Lemma split_sub_product_mod k x y :
 (k-(x mod canonical_group_order)*y) mod canonical_group_order=(k-x*y) mod canonical_group_order.
Proof.
 rewrite (Zminus_mod k ((x mod canonical_group_order)*y) canonical_group_order).
 rewrite (Zminus_mod k (x*y) canonical_group_order).
 rewrite Z.mul_mod_idemp_l by exact split_order_nonzero;reflexivity.
Qed.
Lemma split_lattice_residue k c1 c2 :
 (k-(split_basis_value true*c1-split_lattice_b2*c2)*canonical_lambda_value) mod canonical_group_order=
 (k-split_lattice_b2*c1-split_lattice_a2*c2) mod canonical_group_order.
Proof.
 replace (k-(split_basis_value true*c1-split_lattice_b2*c2)*canonical_lambda_value) with
  (k-(split_basis_value true*canonical_lambda_value)*c1-(-split_lattice_b2*canonical_lambda_value)*c2) by ring.
 destruct split_lattice_relations as [R1 R2];rewrite R1,R2.
 replace (k-(split_lattice_b2+split_lattice_q1*canonical_group_order)*c1-
  (split_lattice_a2+split_lattice_q2*canonical_group_order)*c2) with
  ((k-split_lattice_b2*c1-split_lattice_a2*c2)+(-split_lattice_q1*c1-split_lattice_q2*c2)*canonical_group_order) by ring.
 rewrite Z.mod_add by exact split_order_nonzero;reflexivity.
Qed.

Theorem split_first_signed k : split_first_value k=split_signed_first k mod canonical_group_order.
Proof.
 unfold split_first_value,split_negated_value,split_lambda_product.
 rewrite split_negate_sum_mod,split_second_signed,split_sub_product_mod.
 unfold split_signed_first,split_signed_second;apply split_lattice_residue.
Qed.

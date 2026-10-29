(** Exact curve order and universal annihilator. Internal implication lemmas
    expose the certificate flow; the final results discharge it and are closed. *)
From Coq Require Import ZArith Znumtheory Lia.
From Coqprime.elliptic Require Import SMain.
From Coqprime Require Import EGroup FGroup.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_odd
 C.jet_secp_fe_math C.jet_secp_canonical_scalar C.jet_secp_scalar_prime.
Require Import C.jet_secp_curve_group_power C.jet_secp_curve_group_certificate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma secp_scalar_order_positive:0<canonical_group_order.
Proof. pose proof canonical_group_order_range;lia. Qed.
Theorem secp_generator_order_from_multiple:
 EGroup.gpow secp_group_generator secp_curve_group canonical_group_order=secp_group_infinity ->
 EGroup.e_order (SMain.ceqb secp_group_theory) secp_group_generator secp_curve_group=canonical_group_order.
Proof.
 intro Multiple;eapply (EGroup.order_div secp_group_point (SMain.ceqb secp_group_theory)
  secp_group_add secp_group_generator secp_curve_group canonical_group_order).
 - exact secp_scalar_order_positive.
 - intros p Prime Div.
   pose proof (prime_divisors canonical_group_order secp256k1_scalar_prime p Div) as Alternatives.
   pose proof (prime_ge_2 p Prime) as PPos;pose proof secp_scalar_order_positive as NPos.
   assert (Same:p=canonical_group_order) by (clear -Alternatives PPos NPos;intuition lia).
   rewrite Same,Z.div_same by (pose proof secp_scalar_order_positive;lia).
   change (EGroup.gpow secp_group_generator secp_curve_group 1<>secp_group_infinity).
   rewrite secp_group_power_one;exact secp_group_generator_nonzero.
 - exact (secp_group_points_complete secp_group_generator).
 - change (EGroup.gpow secp_group_generator secp_curve_group canonical_group_order=secp_group_infinity).
   exact Multiple.
Qed.
Theorem secp_curve_group_order_from_multiple:
 EGroup.gpow secp_group_generator secp_curve_group canonical_group_order=secp_group_infinity ->
 FGroup.g_order secp_curve_group=canonical_group_order.
Proof.
 intro Multiple.
 pose proof (EGroup.e_order_divide_g_order secp_group_point (SMain.ceqb secp_group_theory)
  secp_group_add secp_group_generator secp_curve_group (secp_group_points_complete secp_group_generator)) as Divides.
 change (EGroup.e_order (SMain.ceqb secp_group_theory) secp_group_generator secp_curve_group | FGroup.g_order secp_curve_group) in Divides.
 rewrite (secp_generator_order_from_multiple Multiple) in Divides.
 destruct Divides as [k K].
 pose proof secp_curve_group_order_bound as Bound.
 pose proof secp_curve_group_order_positive as Positive.
 pose proof secp_scalar_order_positive as NPos.
 assert (Window:2*feP+1<3*canonical_group_order) by (vm_compute;reflexivity).
 destruct secp_curve_group_order_odd as [z Odd].
 assert (Small:0<k<3) by (clear -K Bound Positive NPos Window;nia).
 assert (Cases:k=1 \/k=2) by lia.
 destruct Cases as [One|Two];[rewrite One in K;lia|rewrite Two in K;lia].
Qed.
Theorem secp_curve_group_annihilator_from_multiple:
 EGroup.gpow secp_group_generator secp_curve_group canonical_group_order=secp_group_infinity ->
 forall point:secp_group_point,EGroup.gpow point secp_curve_group canonical_group_order=secp_group_infinity.
Proof.
 intros Multiple point;rewrite <-(secp_curve_group_order_from_multiple Multiple).
 change (EGroup.gpow point secp_curve_group (FGroup.g_order secp_curve_group)=FGroup.e secp_curve_group).
 apply (EGroup.fermat_gen secp_group_point (SMain.ceqb secp_group_theory) secp_group_add point secp_curve_group).
 exact (secp_group_points_complete point).
Qed.

Theorem secp_curve_group_order_checked:FGroup.g_order secp_curve_group=canonical_group_order.
Proof. apply secp_curve_group_order_from_multiple;exact secp_generator_order_multiple. Qed.
Theorem secp_curve_group_annihilator_checked (point:secp_group_point):
 EGroup.gpow point secp_curve_group canonical_group_order=secp_group_infinity.
Proof. apply secp_curve_group_annihilator_from_multiple;exact secp_generator_order_multiple. Qed.

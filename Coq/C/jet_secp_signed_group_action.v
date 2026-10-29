(** Group action facts needed by signed wNAF and the GLV residue bridge. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import SMain.
From Coqprime Require Import EGroup FGroup.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_power
 C.jet_secp_curve_group_order C.jet_secp_curve_group_scalar_sign C.jet_secp_curve_group_lambda
 C.jet_secp_canonical_scalar C.jet_secp_scalar_prime C.jet_secp_curve_group_odd.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque EGroup.gpow secp_curve_group secp_group_infinity SMain.add SMain.opp.
Lemma secp_group_power_infinity k:0<=k ->
 EGroup.gpow secp_group_infinity secp_curve_group k=secp_group_infinity.
Proof. exact (EGroup.gpow_e secp_group_point secp_group_add secp_curve_group k). Qed.
Lemma secp_group_add_infinity_l (p:secp_group_point):SMain.add secp_group_theory secp_group_infinity p=p.
Proof. exact (FGroup.e_is_zero_l secp_curve_group p (secp_group_points_complete p)). Qed.
Lemma secp_group_power_mod (p:secp_group_point) (k:Z):0<=k ->
 EGroup.gpow p secp_curve_group k=EGroup.gpow p secp_curve_group (k mod canonical_group_order).
Proof.
 intro Nonnegative;pose proof secp_scalar_order_positive as Positive.
 pose proof (Z.div_mod k canonical_group_order ltac:(lia)) as Division.
 pose proof (Z.mod_pos_bound k canonical_group_order Positive) as Remainder.
 assert (Quotient:0<=k/canonical_group_order) by (apply Z.div_pos;lia).
 replace k with (canonical_group_order*(k/canonical_group_order)+k mod canonical_group_order) at 1 by lia.
 rewrite secp_group_power_add by nia.
 rewrite secp_group_power_multiply by lia.
 rewrite secp_curve_group_annihilator_checked,secp_group_power_infinity by lia.
 apply secp_group_add_infinity_l.
Qed.

Require Import C.jet_secp_lookup5_group.
Lemma secp_group_signed_power_mod (p:secp_group_point) (k:Z):
 secp_group_signed_power p k=EGroup.gpow p secp_curve_group (k mod canonical_group_order).
Proof.
 unfold secp_group_signed_power;destruct (k <? 0) eqn:Negative.
 - apply Z.ltb_lt in Negative.
   rewrite (secp_group_power_mod p (-k)) by lia.
   pose proof (Z.mod_pos_bound (-k) canonical_group_order secp_scalar_order_positive) as Range.
   transitivity (EGroup.gpow (SMain.opp secp_group_theory p) secp_curve_group ((-k) mod canonical_group_order)).
   { symmetry;apply secp_group_power_opp;lia. }
   transitivity (EGroup.gpow p secp_curve_group
     ((canonical_group_order-((-k) mod canonical_group_order)) mod canonical_group_order)).
   { symmetry;apply secp_group_scalar_negation;exact Range. }
   apply f_equal;rewrite Zminus_mod_idemp_r.
   replace (canonical_group_order- -k) with (k+1*canonical_group_order) by ring.
   rewrite Z.mod_add by (pose proof secp_scalar_order_positive;lia);reflexivity.
 - apply Z.ltb_ge in Negative;apply secp_group_power_mod;exact Negative.
Qed.
Local Opaque secp_group_signed_power.
Lemma secp_group_signed_power_add (p:secp_group_point) (k m:Z):
 secp_group_signed_power p (k+m)=
 SMain.add secp_group_theory (secp_group_signed_power p k) (secp_group_signed_power p m).
Proof.
 rewrite !secp_group_signed_power_mod.
 pose proof (Z.mod_pos_bound k canonical_group_order secp_scalar_order_positive) as K.
 pose proof (Z.mod_pos_bound m canonical_group_order secp_scalar_order_positive) as M.
 transitivity (EGroup.gpow p secp_curve_group
  ((k mod canonical_group_order+m mod canonical_group_order) mod canonical_group_order)).
 { apply f_equal;apply Z.add_mod;pose proof secp_scalar_order_positive;lia. }
 transitivity (EGroup.gpow p secp_curve_group (k mod canonical_group_order+m mod canonical_group_order)).
 { symmetry;apply secp_group_power_mod;lia. }
 apply secp_group_power_add;lia.
Qed.
Lemma secp_group_signed_power_multiply (p:secp_group_point) (k m:Z):
 secp_group_signed_power (secp_group_signed_power p k) m=secp_group_signed_power p (k*m).
Proof.
 rewrite !secp_group_signed_power_mod.
 pose proof (Z.mod_pos_bound k canonical_group_order secp_scalar_order_positive) as K.
 pose proof (Z.mod_pos_bound m canonical_group_order secp_scalar_order_positive) as M.
 transitivity (EGroup.gpow p secp_curve_group
  (k mod canonical_group_order*(m mod canonical_group_order))).
 { symmetry;apply secp_group_power_multiply;lia. }
 transitivity (EGroup.gpow p secp_curve_group
  ((k mod canonical_group_order*(m mod canonical_group_order)) mod canonical_group_order)).
 { apply secp_group_power_mod;nia. }
 apply f_equal;symmetry;apply Z.mul_mod;pose proof secp_scalar_order_positive;lia.
Qed.
Local Transparent secp_group_signed_power.
Lemma secp_group_signed_power_nonnegative (p:secp_group_point) (k:Z):0<=k ->
 secp_group_signed_power p k=EGroup.gpow p secp_curve_group k.
Proof.
 intro Nonnegative;unfold secp_group_signed_power.
 destruct (k <? 0) eqn:Negative;[apply Z.ltb_lt in Negative;lia|reflexivity].
Qed.
Local Opaque secp_group_signed_power.
Lemma secp_group_signed_power_congruent (p:secp_group_point) (k m:Z):
 k mod canonical_group_order=m mod canonical_group_order ->
 secp_group_signed_power p k=secp_group_signed_power p m.
Proof. intro Congruent;rewrite !secp_group_signed_power_mod,Congruent;reflexivity. Qed.
Require Import C.jet_secp_curve_group_endomorphism C.jet_secp_scalar_lambda_global
 C.jet_secp_canonical_scalar_lambda.
Lemma secp_group_signed_endo_action (p:secp_group_point) (k:Z):
 secp_group_signed_power (secp_group_endomorphism p) k=
 secp_group_signed_power p (canonical_lambda_value*k).
Proof.
 transitivity (secp_group_signed_power (secp_group_signed_power p canonical_lambda_value) k).
 - apply (f_equal (fun q=>secp_group_signed_power q k)).
   transitivity (EGroup.gpow p secp_curve_group canonical_lambda_value).
   + apply secp_group_lambda_action.
   + symmetry;apply secp_group_signed_power_nonnegative;pose proof canonical_lambda_value_range;lia.
 - apply secp_group_signed_power_multiply.
Qed.
Lemma secp_group_signed_glv (p:secp_group_point) (k a b:Z):
 (a+canonical_lambda_value*b) mod canonical_group_order=k mod canonical_group_order ->
 SMain.add secp_group_theory (secp_group_signed_power p a)
  (secp_group_signed_power (secp_group_endomorphism p) b)=secp_group_signed_power p k.
Proof.
 intro Residue;rewrite secp_group_signed_endo_action.
 transitivity (secp_group_signed_power p (a+canonical_lambda_value*b)).
 - symmetry;apply secp_group_signed_power_add.
 - apply secp_group_signed_power_congruent;exact Residue.
Qed.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_split_numeric C.jet_secp_split_constants C.jet_secp_split_signed_bounds
 C.jet_secp_split_literal C.jet_secp_split_half_numeric C.jet_secp_wnaf5_input.
Lemma secp_split_group_residue k:
 (split_first_value k+canonical_lambda_value*split_second_value k) mod canonical_group_order=
 k mod canonical_group_order.
Proof.
 unfold split_first_value,split_negated_value,split_lambda_product.
 rewrite split_negate_sum_mod,Z.add_mod_idemp_l by (pose proof secp_scalar_order_positive;lia).
 f_equal;ring.
Qed.
Theorem secp_literal_split_group (p:secp_group_point) (raw:Ty.tySem (Word 8)):
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 SMain.add secp_group_theory (secp_group_signed_power p (split_half_signed (fst halves)))
  (secp_group_signed_power (secp_group_endomorphism p) (split_half_signed (snd halves)))=
 secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)).
Proof.
 cbn zeta;apply secp_group_signed_glv.
 pose proof (literal_scalar_split_lambda_residues raw) as [First Second].
 rewrite split_half_residue in First,Second.
 transitivity ((split_first_value (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))+
   canonical_lambda_value*split_second_value (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))) mod canonical_group_order).
 - rewrite <-First,<-Second.
   assert (Congruence:forall a b:Z,
    (a+canonical_lambda_value*b) mod canonical_group_order=
    (a mod canonical_group_order+canonical_lambda_value*(b mod canonical_group_order)) mod canonical_group_order).
   { intros a b.
     rewrite (Z.add_mod a (canonical_lambda_value*b) canonical_group_order) by (pose proof secp_scalar_order_positive;lia).
     rewrite (Z.add_mod (a mod canonical_group_order) (canonical_lambda_value*(b mod canonical_group_order)) canonical_group_order)
       by (pose proof secp_scalar_order_positive;lia).
     rewrite Z.mod_mod,Z.mul_mod_idemp_r by (pose proof secp_scalar_order_positive;lia).
     reflexivity. }
   apply Congruence.
 - apply secp_split_group_residue.
Qed.

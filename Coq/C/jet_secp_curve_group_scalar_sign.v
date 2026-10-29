(** Transfer the sign convention used differently by the original C and
    canonical Simplicity Schnorr predicates. This uses the checked curve-order
    certificate; it adds no public premise. The literal Strauss adapter is
    separate and is not established by these group identities. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_power
 C.jet_secp_curve_group_order C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_negate.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma secp_group_opp_infinity:SMain.opp secp_group_theory secp_group_infinity=secp_group_infinity.
Proof. reflexivity. Qed.
Local Opaque SMain.add SMain.opp.
Lemma secp_group_positive_power_opp point k:
 secp_group_power_pos (SMain.opp secp_group_theory point) k=
 SMain.opp secp_group_theory (secp_group_power_pos point k).
Proof.
 induction k as [k IH|k IH|];cbn [secp_group_power_pos];unfold secp_group_add.
 - rewrite !SMain.opp_add,IH;reflexivity.
 - rewrite SMain.opp_add,IH;reflexivity.
 - reflexivity.
Qed.
Lemma secp_group_power_zero point:EGroup.gpow point secp_curve_group 0=secp_group_infinity.
Proof. reflexivity. Qed.
Lemma secp_group_power_opp point k:0<=k ->
 EGroup.gpow (SMain.opp secp_group_theory point) secp_curve_group k=
 SMain.opp secp_group_theory (EGroup.gpow point secp_curve_group k).
Proof.
 intro Nonnegative;destruct k as [|k|k].
 - rewrite !secp_group_power_zero;rewrite secp_group_opp_infinity;reflexivity.
 - transitivity (secp_group_power_pos (SMain.opp secp_group_theory point) k).
   + symmetry;apply secp_group_power_pos_correct.
   + rewrite secp_group_positive_power_opp;f_equal;apply secp_group_power_pos_correct.
 - lia.
Qed.
Lemma secp_group_scalar_negation point e:0<=e<canonical_group_order ->
 EGroup.gpow point secp_curve_group ((canonical_group_order-e) mod canonical_group_order)=
 EGroup.gpow (SMain.opp secp_group_theory point) secp_curve_group e.
Proof.
 intro Range;destruct (Z.eq_dec e 0) as [Zero|Nonzero].
 - subst e;rewrite Z.sub_0_r,Z.mod_same by (pose proof secp_scalar_order_positive;lia).
   rewrite !secp_group_power_zero;reflexivity.
 - rewrite Z.mod_small by lia.
   rewrite secp_group_power_opp by lia.
   apply (SMain.uniq_opp secp_group_theory (EGroup.gpow point secp_curve_group e)
    (EGroup.gpow point secp_curve_group (canonical_group_order-e))).
   change (secp_group_add (EGroup.gpow point secp_curve_group e)
    (EGroup.gpow point secp_curve_group (canonical_group_order-e))=secp_group_infinity).
   rewrite <-secp_group_power_add by lia.
   replace (e+(canonical_group_order-e)) with canonical_group_order by ring.
   apply secp_curve_group_annihilator_checked.
Qed.
Local Opaque EGroup.gpow canonical_scalar_negate canonical_scalar_normalize toZ.
Theorem secp_group_normalized_scalar_sign point (raw:Ty.tySem (Word 8)):
 EGroup.gpow point secp_curve_group
  (@toZ (WordToZ 8) (@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw)))=
 EGroup.gpow (SMain.opp secp_group_theory point) secp_curve_group
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)).
Proof.
 rewrite canonical_scalar_negate_numeric.
 remember (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)) as e eqn:E.
 assert (Range:0<=e<canonical_group_order).
 { rewrite E,canonical_scalar_normalize_numeric;apply Z.mod_pos_bound;exact secp_scalar_order_positive. }
 replace (-e mod canonical_group_order) with ((canonical_group_order-e) mod canonical_group_order).
 - apply secp_group_scalar_negation;exact Range.
 - clear -e.
   replace (canonical_group_order-e) with (-e+1*canonical_group_order) by ring.
   rewrite Z.mod_add by (pose proof secp_scalar_order_positive;lia);reflexivity.
Qed.

(** Fast, proved coefficient reduction for polynomial certificates. This is
    proof computation only; no C implementation or specification is replaced. *)
From Coq Require Import ZArith Lia Ring.
Require Import C.jet_secp_fe_math.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_fold_coefficient a :=
 Z.land a (Z.ones 256)+feR*Z.shiftr a 256.

Lemma secp_fold_coefficient_mod a :
 secp_fold_coefficient a mod feP=a mod feP.
Proof.
 unfold secp_fold_coefficient;rewrite Z.land_ones,Z.shiftr_div_pow2 by lia.
 pose proof (Z.div_mod a (2^256) ltac:(lia)) as Divide.
 assert (Fold:a mod 2^256+feR*(a/2^256)=a+(-(a/2^256))*feP).
 { unfold feP;nia. }
 rewrite Fold,Z.mod_add by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma secp_fold_coefficient_bound a b : 0<=a<2^256*b ->
 0<=secp_fold_coefficient a<2^256+feR*b.
Proof.
 intro Bound;unfold secp_fold_coefficient.
 rewrite Z.land_ones,Z.shiftr_div_pow2 by lia.
 pose proof (Z.mod_pos_bound a (2^256) ltac:(lia)) as Low.
 pose proof (Z.div_pos a (2^256) ltac:(lia) ltac:(lia)) as Nonnegative.
 pose proof (Z.div_lt_upper_bound a (2^256) b ltac:(lia) ltac:(lia)) as High.
 unfold feR;nia.
Qed.

Definition secp_positive_remainder a :=
 let r:=secp_fold_coefficient (secp_fold_coefficient (secp_fold_coefficient a)) in
 if Z.ltb r feP then r else r-feP.

Lemma secp_positive_remainder_correct a : 0<=a<2^512 ->
 secp_positive_remainder a=a mod feP.
Proof.
 intro Bound.
 assert (First:0<=secp_fold_coefficient a<2^256*(feR+1)).
 { pose proof (secp_fold_coefficient_bound a (2^256) ltac:(replace (2^256*2^256) with (2^512) by reflexivity;lia));nia. }
 assert (Second:0<=secp_fold_coefficient (secp_fold_coefficient a)<2^256*2).
 { pose proof (secp_fold_coefficient_bound (secp_fold_coefficient a) (feR+1) First).
   unfold feR in *;lia. }
 pose proof (secp_fold_coefficient_bound (secp_fold_coefficient (secp_fold_coefficient a)) 2 Second) as Third.
 set (r:=secp_fold_coefficient (secp_fold_coefficient (secp_fold_coefficient a))) in *.
 assert (Range:0<=r<2*feP) by (unfold feP,feR in *;lia).
 assert (Same:r mod feP=a mod feP).
 { unfold r;rewrite !secp_fold_coefficient_mod;reflexivity. }
 unfold secp_positive_remainder;fold r.
 destruct (Z.ltb r feP) eqn:Less.
 - apply Z.ltb_lt in Less;rewrite <-Same;rewrite Z.mod_small by lia;reflexivity.
 - apply Z.ltb_ge in Less;rewrite <-Same.
   replace r with ((r-feP)+1*feP) at 2 by ring.
   rewrite Z.mod_add,Z.mod_small by (unfold feP,feR in *;lia);reflexivity.
Qed.

Definition secp_coefficient_remainder a :=
 if Z.ltb a 0 then
  if Z.ltb (-feP) a then a+feP else a mod feP
 else if Z.ltb a (2^512) then secp_positive_remainder a else a mod feP.

Theorem secp_coefficient_remainder_correct a :
 secp_coefficient_remainder a=a mod feP.
Proof.
 unfold secp_coefficient_remainder;destruct (Z.ltb a 0) eqn:Negative.
 - apply Z.ltb_lt in Negative;destruct (Z.ltb (-feP) a) eqn:Small;[|reflexivity].
   apply Z.ltb_lt in Small.
   replace a with ((a+feP)+(-1)*feP) at 2 by ring.
   rewrite Z.mod_add,Z.mod_small by (unfold feP,feR in *;lia);reflexivity.
 - apply Z.ltb_ge in Negative;destruct (Z.ltb a (2^512)) eqn:Small;[|reflexivity].
   apply Z.ltb_lt in Small;apply secp_positive_remainder_correct;lia.
Qed.

Definition polynomial_coefficient_remainder modulus a :=
 if Z.eqb modulus feP then secp_coefficient_remainder a else a mod modulus.

Theorem polynomial_coefficient_remainder_correct modulus a :
 polynomial_coefficient_remainder modulus a=a mod modulus.
Proof.
 unfold polynomial_coefficient_remainder;destruct (Z.eqb modulus feP) eqn:Equal;[|reflexivity].
 apply Z.eqb_eq in Equal;subst modulus;apply secp_coefficient_remainder_correct.
Qed.

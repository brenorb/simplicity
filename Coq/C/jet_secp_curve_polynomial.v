(** Soundness of finite-field root exclusion certificates for the original
    secp256k1 odd table. Concrete coefficient lists remain untrusted data. *)
From Coq Require Import ZArith Znumtheory Zpow_facts List Lia Ring.
From Coqprime Require Import Zp Euler.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_polynomial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma secp_field_power_one a : a mod feP<>0 -> a^(feP-1) mod feP=1.
Proof.
 intro Nonzero.
 rewrite <-(prime_phi_n_minus_1 feP secp256k1_field_prime).
 apply phi_power_is_1.
 - unfold feP,feR;lia.
 - apply rel_prime_sym;apply prime_rel_prime;[exact secp256k1_field_prime|].
   intro Divides;apply Nonzero.
   apply (proj2 (Z.mod_divide a feP ltac:(unfold feP,feR;lia)));exact Divides.
Qed.

Definition secp_euler_exponent : positive :=
  Z.to_pos ((feP-1)/2).

Lemma secp_euler_exponent_value :
 Z.pos secp_euler_exponent=(feP-1)/2 /\
 2*Z.pos secp_euler_exponent=feP-1.
Proof. vm_compute;split;reflexivity. Qed.

Lemma secp_square_character y :
 (y*y)^Z.pos secp_euler_exponent mod feP=0 \/
 (y*y)^Z.pos secp_euler_exponent mod feP=1.
Proof.
 assert (Positive:0<feP) by (unfold feP,feR;lia).
 destruct (Z.eq_dec (y mod feP) 0) as [Zero|Nonzero].
 - left;rewrite Zpower_mod by exact Positive.
   rewrite Z.mul_mod,Zero,Z.mul_0_l,Z.mod_0_l by lia.
   reflexivity.
 - right;replace (y*y) with (y^2) by ring.
   rewrite <-Z.pow_mul_r by lia.
   rewrite (proj2 secp_euler_exponent_value).
   apply secp_field_power_one;exact Nonzero.
Qed.

Definition secp_cubic_exponent : positive := Z.to_pos ((feP-1)/3).
Definition secp_cubic_curve_polynomial : list Z := [7;1].

Lemma secp_cubic_exponent_value : 3*Z.pos secp_cubic_exponent=feP-1.
Proof. vm_compute;reflexivity. Qed.

Lemma secp_cubic_character x : x mod feP<>0 ->
 (x*x*x)^Z.pos secp_cubic_exponent mod feP=1.
Proof.
 intro Nonzero;replace (x*x*x) with (x^3) by ring.
 rewrite <-Z.pow_mul_r by lia;rewrite secp_cubic_exponent_value.
 apply secp_field_power_one;exact Nonzero.
Qed.

Lemma secp_seven_character :
 Zpow_mod 7 (Z.pos secp_euler_exponent) feP=feP-1.
Proof. vm_compute;reflexivity. Qed.

Lemma secp_curve_x_nonzero x y :
 (x*x*x+7) mod feP=(y*y) mod feP -> x mod feP<>0.
Proof.
 intros Curve Zero.
 assert (Positive:0<feP) by (unfold feP,feR;lia).
 assert (Seven:(y*y) mod feP=7 mod feP).
 { rewrite Z.add_mod,(Z.mul_mod (x*x)),(Z.mul_mod x),Zero in Curve by lia.
   change ((7 mod feP) mod feP=(y*y) mod feP) in Curve.
   rewrite Z.mod_mod in Curve by lia.
   symmetry;exact Curve. }
 assert (Character:(y*y)^Z.pos secp_euler_exponent mod feP=feP-1).
 { rewrite Zpower_mod,Seven,<-Zpower_mod by exact Positive.
   rewrite <-Zpow_mod_correct by lia;exact secp_seven_character. }
 destruct (secp_square_character y);unfold feP,feR in *;lia.
Qed.

(** Compressing the table polynomials in t=x^3 reduces the largest degree
    from 112 to 37. Rational cubes satisfy this stronger power identity. *)
Lemma secp_polynomial_cubic_factor q power d u v t :
 polynomial_power feP [0;1] secp_cubic_exponent q=power ->
 polynomial_add feP (polynomial_mul feP u q)
  (polynomial_mul feP v (polynomial_sub feP power [1]))=d ->
 t^Z.pos secp_cubic_exponent mod feP=1 ->
 polynomial_value q t mod feP=0 -> polynomial_value d t mod feP=0.
Proof.
 intros Power Bezout Cube Root.
 assert (Nonzero:feP<>0) by (unfold feP,feR;lia).
 assert (PowerValue:polynomial_value power t mod feP=1).
 { rewrite <-Power,polynomial_power_value by assumption.
   cbn [polynomial_value];rewrite Z.mul_0_r,Z.add_0_r,Z.mul_1_r,Z.add_0_l;exact Cube. }
 rewrite <-Bezout,polynomial_add_value,Z.add_mod by exact Nonzero.
 rewrite !polynomial_mul_value by exact Nonzero.
 rewrite (Z.mul_mod (polynomial_value u t)),Root,Z.mul_0_r,Z.mod_0_l by exact Nonzero.
 rewrite Z.add_0_l,Z.mod_mod,Z.mul_mod,polynomial_sub_value,Zminus_mod,PowerValue by exact Nonzero.
 cbn [polynomial_value];rewrite Z.mul_0_r,Z.add_0_r,(Z.mod_small 1 feP) by (unfold feP,feR;lia).
 rewrite Z.sub_diag,Z.mod_0_l,Z.mul_0_r,Z.mod_0_l by exact Nonzero;reflexivity.
Qed.

Theorem secp_cubic_polynomial_excludes_root q power d u v x y :
 polynomial_power feP [0;1] secp_cubic_exponent q=power ->
 polynomial_add feP (polynomial_mul feP u q)
  (polynomial_mul feP v (polynomial_sub feP power [1]))=d ->
 (d=[1] \/ polynomial_power feP secp_cubic_curve_polynomial secp_euler_exponent d=[feP-1]) ->
 (x*x*x+7) mod feP=(y*y) mod feP ->
 polynomial_value q (x*x*x) mod feP<>0.
Proof.
 intros Power Bezout Euler Curve Root.
 assert (Positive:0<feP) by (unfold feP,feR;lia).
 pose proof (secp_curve_x_nonzero x y Curve) as Nonzero.
 pose proof (secp_cubic_character x Nonzero) as Cube.
 pose proof (secp_polynomial_cubic_factor q power d u v (x*x*x) Power Bezout Cube Root) as Factor.
 destruct Euler as [One|Euler].
 - rewrite One in Factor;cbn [polynomial_value] in Factor.
   rewrite Z.mul_0_r,Z.add_0_r,Z.mod_small in Factor by (unfold feP,feR;lia);discriminate.
 - pose proof (polynomial_power_value feP secp_cubic_curve_polynomial secp_euler_exponent d
    (x*x*x) ltac:(lia) Factor) as Character.
   rewrite Euler in Character;cbn [polynomial_value] in Character.
   rewrite Z.mul_0_r,Z.add_0_r,Z.mod_small in Character by (unfold feP,feR;lia).
   assert (CurveValue:polynomial_value secp_cubic_curve_polynomial (x*x*x)=x*x*x+7).
   { unfold secp_cubic_curve_polynomial;cbn [polynomial_value];ring. }
   rewrite CurveValue in Character.
   rewrite (Zpower_mod (x*x*x+7)),Curve,<-Zpower_mod in Character by exact Positive.
   destruct (secp_square_character y);unfold feP,feR in *;lia.
Qed.


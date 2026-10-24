(** Selection obligations for the original SWU mapper. This module proves
    success of the third actual root check from a square-product witness,
    not that the three source candidates have that product. The latter
    algebra and the implementation's call composition remain to be linked. *)
From Coq Require Import ZArith Znumtheory Lia Ring.
From Coqprime Require Import Zp ZCAux Euler.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime
  C.jet_secp_root_check C.jet_secp_swu_root_power.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma swu_euler_exponent_twice : 2*((feP-1)/2)=feP-1.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_square_character a : a mod feP<>0 -> (a*a)^((feP-1)/2) mod feP=1.
Proof.
  intro Nonzero;rewrite <-(Z.pow_2_r a).
  rewrite <-Z.pow_mul_r by (clear;vm_compute;discriminate).
  rewrite swu_euler_exponent_twice;exact (swu_field_fermat a Nonzero).
Qed.
(** Only closed modular exponentiation is computed, never the unbounded
    integer power of this exponent. *)
Lemma swu_minus_eight_character : Zpow_mod (-8) ((feP-1)/2) feP=feP-1.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_minus_eight_not_square a : (a*a) mod feP<>(-8) mod feP.
Proof.
  intro Square;assert (Nonzero:a mod feP<>0).
  { intro Zero;rewrite (Z.mul_mod a a feP),Zero in Square by (unfold feP,feR;lia).
    vm_compute in Square;discriminate. }
  pose proof (swu_square_character a Nonzero) as Character.
  rewrite (Zpower_mod (a*a) ((feP-1)/2) feP) in Character by (unfold feP,feR;lia).
  rewrite Square,<-Zpower_mod in Character by (unfold feP,feR;lia).
  rewrite <-(Zpow_mod_Zpower_correct (-8) ((feP-1)/2) feP
    ltac:(unfold feP,feR;lia) ltac:(vm_compute;discriminate)) in Character.
  rewrite swu_minus_eight_character in Character;unfold feP,feR in Character;lia.
Qed.
Lemma swu_candidate_denominator_nonzero t : (t*t+8) mod feP<>0.
Proof.
  intro Zero;apply (swu_minus_eight_not_square t).
  assert (Eq:((t*t+8)-8) mod feP=(0-8) mod feP).
  { rewrite Zminus_mod,Zero;reflexivity. }
  replace (t*t+8-8) with (t*t) in Eq by ring;exact Eq.
Qed.

Lemma swu_mod_square_one z : (z*z) mod feP=1 ->
  z mod feP=1 \/ z mod feP=feP-1.
Proof.
  intro Square;assert (Div:(feP | (z-1)*(z+1))).
  { apply (proj1 (Z.mod_divide _ feP ltac:(unfold feP,feR;lia))).
    replace ((z-1)*(z+1)) with (z*z-1) by ring.
    rewrite Zminus_mod,Square;reflexivity. }
  destruct (prime_mult feP secp256k1_field_prime (z-1) (z+1) Div) as [Minus|Plus].
  - left;destruct Minus as [k Eq];replace z with (1+k*feP) by lia.
    rewrite Z.mod_add by (unfold feP,feR;lia).
    apply Z.mod_small;unfold feP,feR;lia.
  - right;destruct Plus as [k Eq];replace z with ((feP-1)+(k-1)*feP) by lia.
    rewrite Z.mod_add by (unfold feP,feR;lia).
    apply Z.mod_small;unfold feP,feR;lia.
Qed.
Lemma swu_field_character_sign a : a mod feP<>0 ->
  a^((feP-1)/2) mod feP=1 \/ a^((feP-1)/2) mod feP=feP-1.
Proof.
  intro Nonzero;apply swu_mod_square_one.
  rewrite <-Z.pow_2_r,<-Z.pow_mul_r by (clear;vm_compute;discriminate).
  replace (((feP-1)/2)*2) with (feP-1) by (pose proof swu_euler_exponent_twice;lia).
  exact (swu_field_fermat a Nonzero).
Qed.
Lemma swu_root_power_character a :
  (a^swu_root_exponent*a^swu_root_exponent) mod feP=(a*a^((feP-1)/2)) mod feP.
Proof.
  rewrite <-Z.pow_2_r,<-Z.pow_mul_r by (pose proof swu_root_exponent_bounds;lia).
  replace (swu_root_exponent*2) with (1+(feP-1)/2) by (vm_compute;reflexivity).
  rewrite Z.pow_add_r by (clear;vm_compute;discriminate).
  rewrite Z.pow_1_r;reflexivity.
Qed.
Lemma swu_character_one_square a : a^((feP-1)/2) mod feP=1 ->
  exists b,a mod feP=(b*b) mod feP.
Proof.
  intro Character;exists (a^swu_root_exponent).
  rewrite swu_root_power_character,(Z.mul_mod a (a^((feP-1)/2)) feP),Character,
    Z.mul_1_r,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma swu_nonsquare_nonzero a : (forall b,a mod feP<>(b*b) mod feP) -> a mod feP<>0.
Proof. intros Nonsquare Zero;apply (Nonsquare 0);exact Zero. Qed.
Lemma swu_nonsquare_character a : (forall b,a mod feP<>(b*b) mod feP) ->
  a^((feP-1)/2) mod feP=feP-1.
Proof.
  intro Nonsquare;destruct (swu_field_character_sign a
    (swu_nonsquare_nonzero a Nonsquare)) as [One|Minus];[|exact Minus].
  destruct (swu_character_one_square a One) as [b Square].
  exact (False_rect _ (Nonsquare b Square)).
Qed.
Lemma swu_character_product a b : (a*b)^((feP-1)/2) mod feP=
  ((a^((feP-1)/2) mod feP)*(b^((feP-1)/2) mod feP)) mod feP.
Proof. rewrite Z.pow_mul_l;apply Z.mul_mod;unfold feP,feR;lia. Qed.
Lemma swu_three_nonsquares_not_square a b c :
  (forall r,a mod feP<>(r*r) mod feP) ->
  (forall r,b mod feP<>(r*r) mod feP) ->
  (forall r,c mod feP<>(r*r) mod feP) ->
  forall r,(a*b*c) mod feP<>(r*r) mod feP.
Proof.
  intros A B C r Square.
  pose proof (swu_nonsquare_nonzero a A) as Az.
  pose proof (swu_nonsquare_nonzero b B) as Bz.
  pose proof (swu_nonsquare_nonzero c C) as Cz.
  assert (Rz:r mod feP<>0).
  { intro Zero;pose proof (secp256k1_nonzero_product (a*b) c
      (secp256k1_nonzero_product a b Az Bz) Cz) as Pz.
    apply Pz;rewrite Square,(Z.mul_mod r r feP),Zero by (unfold feP,feR;lia);reflexivity. }
  pose proof (swu_square_character r Rz) as Character.
  rewrite (Zpower_mod (r*r) ((feP-1)/2) feP),<-Square,<-Zpower_mod in Character
    by (unfold feP,feR;lia).
  rewrite swu_character_product,swu_character_product in Character.
  rewrite (swu_nonsquare_character a A),(swu_nonsquare_character b B),
    (swu_nonsquare_character c C) in Character.
  vm_compute in Character;discriminate.
Qed.
Lemma swu_third_root_check_from_product x y z :
  (exists r,(@toZ (WordToZ 8) x * @toZ (WordToZ 8) y * @toZ (WordToZ 8) z) mod feP=
    (r*r) mod feP) ->
  Bit.toBool (literal_root_check x)=false -> Bit.toBool (literal_root_check y)=false ->
  Bit.toBool (literal_root_check z)=true.
Proof.
  intros [r Square] X Y.
  destruct (Bit.toBool (literal_root_check z)) eqn:Z;[reflexivity|].
  exfalso;exact (swu_three_nonsquares_not_square _ _ _
    (swu_literal_root_failure_not_square x X) (swu_literal_root_failure_not_square y Y)
    (swu_literal_root_failure_not_square z Z) r Square).
Qed.
(** Polynomial numerator identity needed when establishing the product for
    the exact mapper coordinates. It alone does not establish that bridge. *)
Lemma swu_candidate_numerator_identity s :
  (s*s-8*s+64)^3+21*(s*s-8*s+64)*(s+8)^4+42*(s+8)^6 =
  -64*((3*s-(s+8)^2)^3+189*s^3).
Proof. ring. Qed.

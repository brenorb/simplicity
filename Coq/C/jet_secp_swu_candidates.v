(** Numeric bridge for the exact SWU constants and joint-inverse formulas in
    C/secp256k1/generator_impl.h. This proves candidate selection for every
    input, including zero. It is not execution of that C function: callers
    must still establish these numeric representations from actual calls,
    and connect the selected coordinates to the literal Simplicity mapper. *)
From Coq Require Import ZArith Znumtheory Lia Ring Field Morphisms Setoid.
From Coqprime Require Import ZCAux.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.modinv C.jet_secp_fe_math C.jet_secp_field_prime
  C.jet_secp_root_check C.jet_secp_swu_root_power C.jet_secp_swu_selection.
Local Open Scope Z_scope.
Set Default Timeout 10.

(** Local field automation for the existing, proved modular inverse. This
    introduces no assumption or alternate execution model. Keep its ring
    registration local: it must not replace consumers' integer ring setup. *)
Definition swu_div a b := a*modInv b feP.
Definition swu_inv a := modInv a feP.
Section SwuCandidateAlgebra.
Local Lemma swu_mod_ring : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp (eqm feP).
Proof. constructor;intros;unfold eqm;f_equal;ring. Qed.
Local Add Relation Z (eqm feP)
  reflexivity proved by (eqm_refl feP) symmetry proved by (eqm_sym feP)
  transitivity proved by (eqm_trans feP) as swu_mod_relation.
Local Add Morphism Z.add with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
  as swu_mod_add.
Proof. exact (Zplus_eqm feP). Qed.
Local Add Morphism Z.mul with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
  as swu_mod_mul.
Proof. exact (Zmult_eqm feP). Qed.
Local Add Morphism Z.sub with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
  as swu_mod_sub.
Proof. exact (Zminus_eqm feP). Qed.
Local Add Morphism Z.opp with signature (eqm feP) ==> (eqm feP) as swu_mod_opp.
Proof. exact (Zopp_eqm feP). Qed.
Local Lemma swu_mod_field :
  field_theory 0 1 Z.add Z.mul Z.sub Z.opp swu_div swu_inv (eqm feP).
Proof.
  constructor.
  - exact swu_mod_ring.
  - unfold eqm;vm_compute;discriminate.
  - intros;reflexivity.
  - intros a Nonzero;unfold eqm,swu_inv;rewrite modInv_mul_l.
    assert (Gcd:Z.gcd a feP=1).
    { apply Zgcd_1_rel_prime;apply rel_prime_sym;apply prime_rel_prime;
        [exact secp256k1_field_prime|].
      intro Div;apply Nonzero;unfold eqm.
      rewrite (proj2 (Z.mod_divide a feP ltac:(unfold feP,feR;lia)) Div);reflexivity. }
    rewrite Gcd;reflexivity.
Qed.
Local Add Morphism swu_inv with signature (eqm feP) ==> (eqm feP) as swu_mod_inv.
Proof. intros x y E;unfold swu_inv;rewrite (modInv_eqm feP x y E);reflexivity. Qed.
Local Add Morphism swu_div with signature (eqm feP) ==> (eqm feP) ==> (eqm feP)
  as swu_mod_div.
Proof.
  intros a b E c d F;unfold swu_div;rewrite (modInv_eqm feP c d F).
  apply (Zmult_eqm feP);[exact E|reflexivity].
Qed.
Local Lemma swu_mod_power : power_theory 1 Z.mul (eqm feP) Z.of_N Z.pow.
Proof.
  constructor;intros r n;unfold eqm;rewrite (rpow_pow_N Zpower_theory);reflexivity.
Qed.
Add Field swu_modfield : swu_mod_field
  (constants [Zcst],power_tac swu_mod_power [Zpow_tac]).

Lemma swu_candidate_pair_identity c s : eqm feP (c*c) (-3) ->
  eqm feP (((c*(8-s)-(s+8))^3+56*(s+8)^3)*((-c*(8-s)-(s+8))^3+56*(s+8)^3))
    (-4096*((3*s-(s+8)^2)^3+189*s^3)).
Proof.
  intro Csquare.
  setoid_replace
    (((c*(8-s)-(s+8))^3+56*(s+8)^3)*((-c*(8-s)-(s+8))^3+56*(s+8)^3)) with
    (3025*(s+8)^6-339*(c*c)*(8-s)^2*(s+8)^4+
       3*(c*c)*(c*c)*(8-s)^4*(s+8)^2-(c*c)*(c*c)*(c*c)*(8-s)^6) by ring.
  setoid_rewrite Csquare;ring.
Qed.

Definition swu_cubic x := x^3+7.
Definition swu_x1 c t := swu_div (c*(8-t*t)-(t*t+8)) (2*(t*t+8)).
Definition swu_x2 c t := swu_div (-c*(8-t*t)-(t*t+8)) (2*(t*t+8)).
Definition swu_x3 t := swu_div (3*t*t-(t*t+8)^2) (3*t*t).
Definition swu_product_factor c t := swu_div (24*c*t^3) ((t*t+8)^3).

Lemma swu_candidate_pair_square c t : eqm feP (c*c) (-3) -> ~eqm feP t 0 ->
  eqm feP (swu_cubic (swu_x1 c t)*swu_cubic (swu_x2 c t))
    (swu_product_factor c t*swu_product_factor c t*swu_cubic (swu_x3 t)).
Proof.
  intros Csquare Tnonzero.
  assert (Wnonzero:~eqm feP (t*t+8) 0) by exact (swu_candidate_denominator_nonzero t).
  unfold swu_x1,swu_x2,swu_x3,swu_product_factor,swu_cubic.
  setoid_replace
    (((swu_div (c*(8-t*t)-(t*t+8)) (2*(t*t+8)))^3+7)*
     ((swu_div (-c*(8-t*t)-(t*t+8)) (2*(t*t+8)))^3+7)) with
    (swu_div (((c*(8-t*t)-(t*t+8))^3+56*(t*t+8)^3)*
      ((-c*(8-t*t)-(t*t+8))^3+56*(t*t+8)^3)) (64*(t*t+8)^6))
    by (field;repeat split;first [assumption|unfold eqm;vm_compute;discriminate]).
  setoid_rewrite (swu_candidate_pair_identity c (t*t) Csquare).
  setoid_replace
    (swu_div (24*c*t^3) ((t*t+8)^3)*swu_div (24*c*t^3) ((t*t+8)^3)) with
    (swu_div (576*(c*c)*t^6) ((t*t+8)^6)) by (field;exact Wnonzero).
  setoid_rewrite Csquare.
  field;repeat split;first [assumption|unfold eqm;vm_compute;discriminate].
Qed.

(** The hexadecimal constants are copied from the unchanged C source. The
    checked modular root equality identifies c with the canonical exponent,
    rather than merely asserting that it is some square root of -3. *)
Definition swu_negc_constant : Z :=
  0xf5d2d456caf80e20dcc88f3d586869d339e092ea25eb132b8272d850e32a03dd.
Definition swu_c_constant : Z := feP-swu_negc_constant.
Definition swu_d_constant : Z :=
  0x851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40.
Lemma swu_constant_square : eqm feP (swu_c_constant*swu_c_constant) (-3).
Proof. unfold eqm,swu_c_constant,swu_negc_constant;vm_compute;reflexivity. Qed.
Lemma swu_negc_constant_link : eqm feP swu_negc_constant (-swu_c_constant).
Proof. unfold eqm,swu_c_constant,swu_negc_constant;vm_compute;reflexivity. Qed.
Lemma swu_d_constant_half : eqm feP swu_d_constant (swu_div (swu_c_constant-1) 2).
Proof.
  unfold eqm,swu_d_constant,swu_div,swu_c_constant,swu_negc_constant;
    vm_compute;reflexivity.
Qed.
Lemma swu_constant_root : Zpow_mod (-3) swu_root_exponent feP=swu_c_constant.
Proof. unfold swu_root_exponent,swu_c_constant,swu_negc_constant;vm_compute;reflexivity. Qed.
Lemma swu_zero_candidate_square : exists r,swu_cubic swu_d_constant mod feP=(r*r) mod feP.
Proof.
  apply swu_character_one_square.
  rewrite <-(Zpow_mod_Zpower_correct (swu_cubic swu_d_constant) ((feP-1)/2) feP
    ltac:(unfold feP,feR;lia) ltac:(vm_compute;discriminate)).
  unfold swu_cubic,swu_d_constant;vm_compute;reflexivity.
Qed.

Definition swu_joint_inverse t := swu_inv ((t*t+8)*(-3*t*t)).
Definition swu_c_candidate1 t :=
  swu_d_constant+swu_negc_constant*t*t*(-3*t*t)*swu_joint_inverse t.
Definition swu_c_candidate2 t := -(swu_c_candidate1 t+1).
Definition swu_c_candidate3 t := 1+(t*t+8)^3*swu_joint_inverse t.
Lemma swu_c_candidate1_bridge t : ~eqm feP t 0 ->
  eqm feP (swu_c_candidate1 t) (swu_x1 swu_c_constant t).
Proof.
  intro Tnonzero;pose proof (swu_candidate_denominator_nonzero t) as Wnonzero.
  unfold swu_c_candidate1,swu_joint_inverse,swu_x1.
  setoid_rewrite swu_negc_constant_link;setoid_rewrite swu_d_constant_half.
  field;repeat split;first [assumption|unfold eqm;vm_compute;discriminate].
Qed.
Lemma swu_c_candidate2_bridge t : ~eqm feP t 0 ->
  eqm feP (swu_c_candidate2 t) (swu_x2 swu_c_constant t).
Proof.
  intro Tnonzero;pose proof (swu_candidate_denominator_nonzero t) as Wnonzero.
  unfold swu_c_candidate2;setoid_rewrite (swu_c_candidate1_bridge t Tnonzero).
  unfold swu_x1,swu_x2.
  field;repeat split;first [assumption|unfold eqm;vm_compute;discriminate].
Qed.
Lemma swu_c_candidate3_bridge t : ~eqm feP t 0 -> eqm feP (swu_c_candidate3 t) (swu_x3 t).
Proof.
  intro Tnonzero;pose proof (swu_candidate_denominator_nonzero t) as Wnonzero.
  unfold swu_c_candidate3,swu_joint_inverse,swu_x3.
  field;repeat split;first [assumption|unfold eqm;vm_compute;discriminate].
Qed.
Local Add Morphism swu_cubic with signature (eqm feP) ==> (eqm feP) as swu_cubic_compat.
Proof.
  intros x y E;unfold swu_cubic,eqm in *.
  rewrite (Zplus_mod (x^3) 7 feP),(Zplus_mod (y^3) 7 feP),
    (Zpower_mod x 3 feP),(Zpower_mod y 3 feP),E by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma swu_c_candidate_product_square t : ~eqm feP t 0 -> exists r,
  (swu_cubic (swu_c_candidate1 t)*swu_cubic (swu_c_candidate2 t)*
    swu_cubic (swu_c_candidate3 t)) mod feP=(r*r) mod feP.
Proof.
  intro Tnonzero;exists (swu_product_factor swu_c_constant t*swu_cubic (swu_x3 t)).
  change (eqm feP
    (swu_cubic (swu_c_candidate1 t)*swu_cubic (swu_c_candidate2 t)*
      swu_cubic (swu_c_candidate3 t))
    ((swu_product_factor swu_c_constant t*swu_cubic (swu_x3 t))*
      (swu_product_factor swu_c_constant t*swu_cubic (swu_x3 t)))).
  setoid_rewrite (swu_c_candidate1_bridge t Tnonzero).
  setoid_rewrite (swu_c_candidate2_bridge t Tnonzero).
  setoid_rewrite (swu_c_candidate3_bridge t Tnonzero).
  setoid_rewrite (swu_candidate_pair_square swu_c_constant t swu_constant_square Tnonzero).
  ring.
Qed.
Lemma swu_c_candidate1_zero t : eqm feP t 0 -> eqm feP (swu_c_candidate1 t) swu_d_constant.
Proof. intro Zero;unfold swu_c_candidate1,swu_joint_inverse;setoid_rewrite Zero;ring. Qed.

(** No nonzero-input restriction: when t=0 the first check already succeeds.
    The three representation premises must be derived from execution in the
    future caller proof, not passed through as new public jet assumptions. *)
Lemma swu_c_candidates_third x y z t :
  eqm feP (@toZ (WordToZ 8) x) (swu_cubic (swu_c_candidate1 t)) ->
  eqm feP (@toZ (WordToZ 8) y) (swu_cubic (swu_c_candidate2 t)) ->
  eqm feP (@toZ (WordToZ 8) z) (swu_cubic (swu_c_candidate3 t)) ->
  Bit.toBool (literal_root_check x)=false -> Bit.toBool (literal_root_check y)=false ->
  Bit.toBool (literal_root_check z)=true.
Proof.
  intros X Y Z FailedX FailedY.
  destruct (Z.eq_dec (t mod feP) 0) as [Zero|Nonzero].
  - assert (Tzero:eqm feP t 0) by exact Zero.
    destruct swu_zero_candidate_square as [r Square].
    assert (Xsquare:@toZ (WordToZ 8) x mod feP=(r*r) mod feP).
    { transitivity (swu_cubic swu_d_constant mod feP);[|exact Square].
      change (eqm feP (@toZ (WordToZ 8) x) (swu_cubic swu_d_constant)).
      etransitivity;[exact X|];apply swu_cubic_compat;apply swu_c_candidate1_zero;exact Tzero. }
    pose proof (swu_literal_root_check_square x r Xsquare) as Good;congruence.
  - apply (swu_third_root_check_from_product x y z);[|exact FailedX|exact FailedY].
    destruct (swu_c_candidate_product_square t Nonzero) as [r Square];exists r.
    transitivity ((swu_cubic (swu_c_candidate1 t)*swu_cubic (swu_c_candidate2 t)*
      swu_cubic (swu_c_candidate3 t)) mod feP);[|exact Square].
    change (eqm feP (@toZ (WordToZ 8) x * @toZ (WordToZ 8) y * @toZ (WordToZ 8) z)
      (swu_cubic (swu_c_candidate1 t)*swu_cubic (swu_c_candidate2 t)*
        swu_cubic (swu_c_candidate3 t))).
    apply (Zmult_eqm feP);[apply (Zmult_eqm feP);assumption|exact Z].
Qed.
(** The literal program inverts -j whereas the C program inverts j. Cover
    the zero denominator too; do not use field cancellation there. *)
Lemma swu_joint_inverse_opposite t :
  eqm feP (swu_inv ((t*t+8)*(3*t*t))) (-swu_joint_inverse t).
Proof.
  destruct (Z.eq_dec (t mod feP) 0) as [Zero|Nonzero].
  - assert (Tzero:eqm feP t 0) by exact Zero.
    assert (PositiveZero:eqm feP ((t*t+8)*(3*t*t)) 0)
      by (setoid_rewrite Tzero;ring).
    assert (NegativeZero:eqm feP ((t*t+8)*(-3*t*t)) 0)
      by (setoid_rewrite Tzero;ring).
    unfold swu_joint_inverse,swu_inv.
    rewrite (modInv_eqm feP _ _ PositiveZero),(modInv_eqm feP _ _ NegativeZero),modInv_zero.
    reflexivity.
  - pose proof (swu_candidate_denominator_nonzero t) as Wnonzero.
    unfold swu_joint_inverse.
    field;repeat split;first [assumption|unfold eqm;vm_compute;discriminate].
Qed.
End SwuCandidateAlgebra.

(** A needed SWU selection bridge, not standalone jet coverage. The original
    C mapper ignores its third sqrt return flag; the literal program does
    not. Connect the already-verified root algorithm to its exact exponent,
    then prove success on squares instead of assuming candidate success. *)
From Coq Require Import ZArith Znumtheory Lia Ring.
From Coqprime Require Import Zp ZCAux Euler.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_root_literal
  C.jet_secp_root_tower_step C.jet_secp_root_chain_numeric C.jet_secp_root_check
  C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_root_square_bridge
  C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program C.jet_secp_canonical_zero.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition swu_root_exponent : Z := (feP+1)/4.
Definition swu_power_match (word:Ty.tySem Word256) a e :=
  @toZ (WordToZ 8) word mod feP=a^e mod feP.

Lemma swu_field_fermat a : a mod feP<>0 -> a^(feP-1) mod feP=1.
Proof.
  intro Nonzero;rewrite <-(prime_phi_n_minus_1 feP secp256k1_field_prime).
  apply phi_power_is_1;[unfold feP,feR;lia|].
  apply rel_prime_sym;apply prime_rel_prime;[exact secp256k1_field_prime|].
  intro Div;apply Nonzero;apply (proj2 (Z.mod_divide a feP ltac:(unfold feP,feR;lia)));exact Div.
Qed.
Lemma swu_root_exponent_bounds : 0<swu_root_exponent.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_root_exponent_four : 4*swu_root_exponent=feP+1.
Proof. vm_compute;reflexivity. Qed.

Lemma swu_power_multiply x y a e f : 0<=e -> 0<=f ->
  swu_power_match x a e -> swu_power_match y a f ->
  swu_power_match (@literal_fe_multiply Alg.CoreFunSem (x,y)) a (e+f).
Proof.
  intros E F X Y;unfold swu_power_match in *.
  rewrite literal_multiply_numeric,Z.mod_mod by (unfold feP,feR;lia).
  rewrite (Z.mul_mod (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) feP) by (unfold feP,feR;lia).
  rewrite X,Y,<-Z.mul_mod by (unfold feP,feR;lia).
  rewrite Z.pow_add_r by lia;reflexivity.
Qed.
Lemma swu_power_square x a e : 0<=e -> swu_power_match x a e ->
  swu_power_match (@literal_fe_square Alg.CoreFunSem x) a (2*e).
Proof.
  intros E X;rewrite literal_square_step;replace (2*e) with (e+e) by ring;
    apply swu_power_multiply;assumption.
Qed.
Lemma swu_power_squares n : forall x a e,0<=e -> swu_power_match x a e ->
  swu_power_match (@literal_fe_squares n Alg.CoreFunSem x) a (2^Z.of_nat n*e).
Proof.
  induction n as [|n IH];intros x a e E X.
  - change (swu_power_match x a (1*e));rewrite Z.mul_1_l;exact X.
  - rewrite literal_fe_squares_successor.
    pose proof (IH (@literal_fe_square Alg.CoreFunSem x) a (2*e) ltac:(lia)
      (swu_power_square x a e E X)) as Power.
    replace (2^Z.of_nat (S n)*e) with (2^Z.of_nat n*(2*e));[exact Power|].
    rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;ring.
Qed.

Local Opaque literal_fe_square literal_fe_multiply literal_fe_squares literal_fe_tower.
(** Follow only the syntactic square/multiply tree. Memoized facts avoid
    replaying shared subchains; VM reduction is confined to closed exponents. *)
Local Ltac swu_derive_power word base continuation :=
  first [match goal with hyp:swu_power_match word base _ |- _=>continuation hyp end |
    lazymatch word with
    | @literal_fe_square Alg.CoreFunSem ?x=>
      swu_derive_power x base ltac:(fun hx=>
        lazymatch type of hx with swu_power_match _ _ ?e=>
          let hp:=fresh "Power" in
          pose proof (swu_power_square x base e ltac:(clear;vm_compute;discriminate) hx) as hp;
          continuation hp end)
    | @literal_fe_multiply Alg.CoreFunSem (?x,?y)=>
      swu_derive_power x base ltac:(fun hx=>swu_derive_power y base ltac:(fun hy=>
        lazymatch type of hx with swu_power_match _ _ ?e=>
        lazymatch type of hy with swu_power_match _ _ ?f=>
          let hp:=fresh "Power" in
          pose proof (swu_power_multiply x y base e f ltac:(clear;vm_compute;discriminate)
            ltac:(clear;vm_compute;discriminate) hx hy) as hp;continuation hp end end))
    | @literal_fe_squares ?n Alg.CoreFunSem ?x=>
      swu_derive_power x base ltac:(fun hx=>
        lazymatch type of hx with swu_power_match _ _ ?e=>
          let hp:=fresh "Power" in
          pose proof (swu_power_squares n x base e ltac:(clear;vm_compute;discriminate) hx) as hp;
          continuation hp end)
    end].

Lemma swu_literal_root_power x :
  swu_power_match (literal_root_candidate x) (@toZ (WordToZ 8) x) swu_root_exponent.
Proof.
  assert (Base:swu_power_match x (@toZ (WordToZ 8) x) 1)
    by (unfold swu_power_match;rewrite Z.pow_1_r;reflexivity).
  unfold literal_root_candidate;rewrite literal_fe_tower_step;cbn [fst snd].
  lazymatch goal with |-swu_power_match ?word ?base _=>
    swu_derive_power word base ltac:(fun hp=>exact hp) end.
(* Checking the shared symbolic addition-chain proof measured about 28 seconds.
   Bound only this proof-closing command; ordinary tactics retain 10 seconds. *)
Set Default Timeout 60.
Qed.
Set Default Timeout 10.

Lemma swu_field_fermat_square a : a^(feP+1) mod feP=(a*a) mod feP.
Proof.
  destruct (Z.eq_dec (a mod feP) 0) as [Zero|Nonzero].
  - rewrite (Zpower_mod a (feP+1) feP) by (unfold feP,feR;lia).
    rewrite Zero,Z.pow_0_l by (unfold feP,feR;lia).
    rewrite (Z.mul_mod a a feP),Zero by (unfold feP,feR;lia);reflexivity.
  - replace (feP+1) with ((feP-1)+2) by ring.
    rewrite Z.pow_add_r by (unfold feP,feR;lia).
    rewrite Z.pow_2_r,(Z.mul_mod (a^(feP-1)) (a*a) feP) by (unfold feP,feR;lia).
    rewrite (swu_field_fermat a Nonzero),Z.mul_1_l,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma swu_power_root_square a :
  (((a*a mod feP)^swu_root_exponent mod feP)^2) mod feP=(a*a) mod feP.
Proof.
  rewrite <-Zpower_mod by (unfold feP,feR;lia).
  rewrite <-Z.pow_mul_r by (pose proof swu_root_exponent_bounds;lia).
  rewrite <-Zpower_mod by (unfold feP,feR;lia).
  replace (a*a) with (a^2) by ring.
  rewrite <-Z.pow_mul_r by (pose proof swu_root_exponent_bounds;lia).
  rewrite Z.pow_2_r;apply swu_field_fermat_square.
Qed.

Local Opaque literal_root_candidate literal_fe_negate literal_fe_add canonical_fe_is_zero.
Lemma swu_literal_root_check_square x a : @toZ (WordToZ 8) x mod feP=(a*a) mod feP ->
  Bit.toBool (literal_root_check x)=true.
Proof.
  intro Square;rewrite literal_root_check_numeric;apply Z.eqb_eq.
  rewrite literal_square_numeric,Z.mod_mod by (unfold feP,feR;lia).
  pose proof (swu_literal_root_power x) as Power;unfold swu_power_match in Power.
  rewrite (Z.mul_mod (@toZ (WordToZ 8) (literal_root_candidate x))
    (@toZ (WordToZ 8) (literal_root_candidate x)) feP) by (unfold feP,feR;lia).
  rewrite Power,<-Z.mul_mod by (unfold feP,feR;lia).
  rewrite <-Z.pow_2_r.
  rewrite (Zpower_mod ((@toZ (WordToZ 8) x)^swu_root_exponent) 2 feP) by (unfold feP,feR;lia).
  rewrite (Zpower_mod (@toZ (WordToZ 8) x) swu_root_exponent feP) by (unfold feP,feR;lia).
  rewrite Square;apply swu_power_root_square.
Qed.
Lemma swu_root_select_true (flag:Bit.Bit) (root:Ty.tySem Word256) : Bit.toBool flag=true ->
  (match flag with inl _=>inl tt|inr _=>inr root end)=inr root.
Proof.
  destruct flag as [u|u];destruct u;
    [intro Impossible;discriminate Impossible|intros;reflexivity].
Qed.
Local Opaque literal_fe_square_root.
Lemma swu_literal_root_success_on_square x a : @toZ (WordToZ 8) x mod feP=(a*a) mod feP ->
  @literal_fe_square_root Alg.CoreFunSem x=inr (literal_root_candidate x).
Proof.
  intro Square;pose proof (swu_literal_root_check_square x a Square) as Good.
  rewrite literal_root_result_step.
  change (match literal_root_check x with inl _=>inl tt | inr _=>inr (literal_root_candidate x) end=
    inr (literal_root_candidate x)).
  exact (swu_root_select_true (literal_root_check x) (literal_root_candidate x) Good).
Qed.
Lemma swu_c_root_check_square w x a : root_words_match w x ->
  @toZ (WordToZ 8) x mod feP=(a*a) mod feP -> root_check_flag w=true.
Proof.
  intros Match Square;rewrite (root_check_flag_matches w x Match);
    exact (swu_literal_root_check_square x a Square).
Qed.
Lemma swu_literal_root_failure_not_square x : Bit.toBool (literal_root_check x)=false ->
  forall a,@toZ (WordToZ 8) x mod feP<>(a*a) mod feP.
Proof.
  intros Failed a Square;pose proof (swu_literal_root_check_square x a Square) as Good;congruence.
Qed.

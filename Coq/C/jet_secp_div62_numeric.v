(** Low-bit arithmetic for the original cancellation words, including the
    real uint32 negation in the four-bit path. No external model is used. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Require Import C.extraMath C.modinv C.jet_secp_div62_cancel C.jet_secp_div62_limit.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma div62_repr_add a b : Int64.add (Int64.repr a) (Int64.repr b)=Int64.repr(a+b).
Proof. unfold Int64.add;apply Int64.eqm_samerepr;auto with ints. Qed.
Lemma div62_repr_sub a b : Int64.sub (Int64.repr a) (Int64.repr b)=Int64.repr(a-b).
Proof. unfold Int64.sub;apply Int64.eqm_samerepr;auto with ints. Qed.
Lemma div62_repr_mul a b : Int64.mul (Int64.repr a) (Int64.repr b)=Int64.repr(a*b).
Proof. unfold Int64.mul;apply Int64.eqm_samerepr;auto with ints. Qed.
Lemma div62_repr_and a b : Int64.and (Int64.repr a) (Int64.repr b)=Int64.repr(Z.land a b).
Proof.
  apply Int64.same_bits_eq;intros j J;rewrite Int64.bits_and,!Int64.testbit_repr by exact J.
  rewrite Z.land_spec;reflexivity.
Qed.
Lemma div62_loword_repr a : Int64.loword (Int64.repr a)=Int.repr a.
Proof.
  apply Int.same_bits_eq;intros j J;rewrite Int64.bits_loword by exact J.
  rewrite Int64.testbit_repr by (change Int64.zwordsize with 64;change Int.zwordsize with 32 in J;lia).
  rewrite Int.testbit_repr by exact J;reflexivity.
Qed.

Lemma div62_repr64_lowbits a k : 0<=k<=64 ->
  Int64.unsigned (Int64.repr a) mod 2^k=a mod 2^k.
Proof.
  intro K;rewrite Int64.unsigned_repr_eq;change (eqm (2^k) (a mod 2^64) a).
  apply (eqm_2_pow_le k 64);[exact K|unfold eqm;rewrite Z.mod_mod by lia;reflexivity].
Qed.
Lemma div62_repr32_lowbits a k : 0<=k<=32 ->
  Int.unsigned (Int.repr a) mod 2^k=a mod 2^k.
Proof.
  intro K;rewrite Int.unsigned_repr_eq;change (eqm (2^k) (a mod 2^32) a).
  apply (eqm_2_pow_le k 32);[exact K|unfold eqm;rewrite Z.mod_mod by lia;reflexivity].
Qed.

Lemma div62_ones_bound k : 0<=k<=64 -> 0<=Z.ones k<=Int64.max_unsigned.
Proof.
  intro K;rewrite Z.ones_equiv;change Int64.max_unsigned with (2^64-1).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_le_mono_r 2 k 64 ltac:(lia) ltac:(lia));lia.
Qed.

Definition div62_cancel_bits (neg : bool) eta i := Z.min (div62_limit eta i) (if neg then 6 else 4).
Lemma div62_cancel_bits_bound neg eta i : 0<=eta<=745 -> 1<=i<=62 ->
  1<=div62_cancel_bits neg eta i<=(if neg then 6 else 4).
Proof.
  intros B I;pose proof (div62_limit_bounds eta i B I);unfold div62_cancel_bits;destruct neg;lia.
Qed.

Theorem div62_mask_value neg eta i : 0<=eta<=745 -> 1<=i<=62 ->
  div62_mask neg eta i=Int64.repr(Z.ones(div62_cancel_bits neg eta i)).
Proof.
  intros B I;pose proof (div62_limit_bounds eta i B I) as L.
  unfold div62_mask,Int64.shru;rewrite Int64.unsigned_mone,Int64.unsigned_repr by
    (change (0<=64-div62_limit eta i<=18446744073709551615);lia).
  change (Int64.modulus-1) with (Z.ones 64).
  rewrite Z_shiftr_ones by lia;replace (64-(64-div62_limit eta i)) with (div62_limit eta i) by lia.
  unfold Int64.and;rewrite (Int64.unsigned_repr (Z.ones (div62_limit eta i))) by
    (apply div62_ones_bound;lia).
  unfold div62_cancel_bits;destruct neg.
  - change (Int64.repr (Z.land (Z.ones (div62_limit eta i)) (Z.ones 6))=
      Int64.repr(Z.ones(Z.min(div62_limit eta i) 6))).
    rewrite Z_land_ones_min by lia;reflexivity.
  - change (Int64.repr (Z.land (Z.ones (div62_limit eta i)) (Z.ones 4))=
      Int64.repr(Z.ones(Z.min(div62_limit eta i) 4))).
    rewrite Z_land_ones_min by lia;reflexivity.
Qed.

Lemma div62_mask_unsigned a k : 0<=k<64 ->
  Int64.unsigned (Int64.and a (Int64.repr(Z.ones k)))=Int64.unsigned a mod 2^k.
Proof.
  intro K;rewrite Z.ones_equiv;change (Z.pred (2^k)) with (2^k-1).
  rewrite <- two_p_equiv,<- Int64.zero_ext_and by lia.
  rewrite Int64.zero_ext_mod by (change Int64.zwordsize with 64;lia).
  rewrite two_p_equiv;reflexivity.
Qed.

Lemma div62_mask_loword a k : 0<=k<=6 ->
  Int.unsigned (Int64.loword (Int64.and a (Int64.repr(Z.ones k))))=Int64.unsigned a mod 2^k.
Proof.
  intro K;unfold Int64.loword;rewrite div62_mask_unsigned by lia.
  apply Int.unsigned_repr.
  pose proof (Z.mod_pos_bound (Int64.unsigned a) (2^k) ltac:(apply Z.pow_pos_nonneg;lia)).
  pose proof (Z.pow_le_mono_r 2 k 6 ltac:(lia) ltac:(lia)).
  change Int.max_unsigned with 4294967295;change (2^6) with 64 in *;lia.
Qed.

Lemma div62_w6_polynomial f g k : 0<=k<=6 ->
  Int.unsigned (div62_w6 (Int64.repr f) (Int64.repr g) (Int64.repr(Z.ones k)))=
    (f*g*(f*f-2)) mod 2^k.
Proof.
  intro K;unfold div62_w6;rewrite !div62_repr_mul,div62_repr_sub,div62_repr_mul.
  rewrite div62_mask_loword,div62_repr64_lowbits by lia;reflexivity.
Qed.

Definition div62_w4_polynomial f := f+Z.shiftl (Z.land (f+1) 4) 1.
Lemma div62_w4_first_value f : div62_w4_first (Int64.repr f)=Int.repr(div62_w4_polynomial f).
Proof.
  unfold div62_w4_first,div62_w4_polynomial;change Int64.one with (Int64.repr 1).
  rewrite div62_repr_add,div62_repr_and,Int64.shl_mul_two_p.
  change (two_p (Int64.unsigned (Int64.repr 1))) with 2.
  rewrite div62_repr_mul,div62_repr_add,div62_loword_repr.
  rewrite Z.shiftl_mul_pow2 by lia;reflexivity.
Qed.

Lemma div62_w4_polynomial_value f g k : 0<=k<=4 ->
  Int.unsigned (div62_w4 (Int64.repr f) (Int64.repr g) (Int64.repr(Z.ones k)))=
    (-div62_w4_polynomial f*g) mod 2^k.
Proof.
  intro K;unfold div62_w4;rewrite div62_w4_first_value,Int.neg_repr,div62_repr_mul.
  rewrite div62_mask_loword,div62_repr64_lowbits by lia.
  rewrite <- Zmult_mod_idemp_l,div62_repr32_lowbits by lia.
  rewrite Zmult_mod_idemp_l;reflexivity.
Qed.

Lemma div62_odd_gcd_power a k : Z.Odd a -> 0<=k -> Z.gcd a (2^k)=1.
Proof.
  intros Odd K;apply Zgcd_1_rel_prime;apply Zpow_facts.rel_prime_Zpower_r;[lia|].
  apply rel_prime_mod_rev;[lia|].
  rewrite Zmod_odd;assert (O : Z.odd a=true) by (apply Z.odd_spec;exact Odd).
  rewrite O;apply rel_prime_1.
Qed.

Lemma div62_inverse_reduce a k n : Z.Odd a -> 1<=k<=n ->
  modInv a (2^n) mod 2^k=modInv a (2^k).
Proof.
  intros Odd K;apply modInv_mul_unique_l.
  assert (Large : eqm (2^n) (modInv a (2^n)*a) 1).
  { unfold eqm;rewrite modInv_mul_l,div62_odd_gcd_power by (assumption || lia);reflexivity. }
  pose proof (eqm_2_pow_le k n _ _ ltac:(lia) Large) as Small.
  unfold eqm in Small;rewrite (Z.mod_small 1 (2^k)) in Small;[exact Small|].
  pose proof (Z.pow_le_mono_r 2 1 k ltac:(lia) ltac:(lia));change (2^1) with 2 in *;lia.
Qed.

Lemma div62_formula_reduce a poly k n : Z.Odd a -> 1<=k<=n ->
  poly mod 2^n=modInv (-a) (2^n) -> poly mod 2^k=modInv (-a) (2^k).
Proof.
  intros Odd K Formula.
  assert (Opp : Z.Odd(-a)).
  { apply Z.odd_spec;rewrite Z.odd_opp;apply Z.odd_spec;exact Odd. }
  assert (Large : eqm (2^n) poly (modInv (-a) (2^n))).
  { unfold eqm;rewrite <- Formula,Z.mod_mod by (apply Z.pow_nonzero;lia);reflexivity. }
  pose proof (eqm_2_pow_le k n _ _ ltac:(lia) Large) as Small.
  unfold eqm in Small;rewrite div62_inverse_reduce in Small by (assumption || lia);exact Small.
Qed.

Theorem div62_w6_inverse f g k : Z.Odd f -> 1<=k<=6 ->
  Int.unsigned (div62_w6 (Int64.repr f) (Int64.repr g) (Int64.repr(Z.ones k)))=
    (modInv (-f) (2^k)*g) mod 2^k.
Proof.
  intros Odd K;rewrite div62_w6_polynomial by lia.
  assert (Formula : (f*(f*f-2)) mod 2^k=modInv (-f) (2^k)).
  { apply (div62_formula_reduce f _ k 6 Odd K).
    rewrite <- Z.land_ones by lia;apply HackersDelightB;exact Odd. }
  replace (f*g*(f*f-2)) with ((f*(f*f-2))*g) by ring.
  rewrite <- Zmult_mod_idemp_l,Formula;reflexivity.
Qed.

Theorem div62_w4_inverse f g k : Z.Odd f -> 1<=k<=4 ->
  Int.unsigned (div62_w4 (Int64.repr f) (Int64.repr g) (Int64.repr(Z.ones k)))=
    (modInv (-f) (2^k)*g) mod 2^k.
Proof.
  intros Odd K;rewrite div62_w4_polynomial_value by lia.
  assert (Formula : (-div62_w4_polynomial f) mod 2^k=modInv (-f) (2^k)).
  { apply (div62_formula_reduce f _ k 4 Odd K).
    unfold div62_w4_polynomial;rewrite <- Z.land_ones by lia;apply HackersDelightA;exact Odd. }
  rewrite <- Zmult_mod_idemp_l,Formula;reflexivity.
Qed.

Theorem div62_w_unsigned neg eta i f g : 0<=eta<=745 -> 1<=i<=62 -> Z.Odd f ->
  Int.unsigned (div62_w_word neg (Int64.repr f) (Int64.repr g) (div62_mask neg eta i))=
    (modInv (-f) (2^div62_cancel_bits neg eta i)*g) mod 2^div62_cancel_bits neg eta i.
Proof.
  intros B I Odd;rewrite div62_mask_value by assumption.
  pose proof (div62_cancel_bits_bound neg eta i B I) as K.
  destruct neg;unfold div62_w_word;[apply div62_w6_inverse|apply div62_w4_inverse];assumption.
Qed.

Corollary div62_w_long_value neg eta i f g : 0<=eta<=745 -> 1<=i<=62 -> Z.Odd f ->
  div62_w_long neg (Int64.repr f) (Int64.repr g) (div62_mask neg eta i)=
    Int64.repr ((modInv (-f) (2^div62_cancel_bits neg eta i)*g) mod 2^div62_cancel_bits neg eta i).
Proof. intros B I Odd;unfold div62_w_long;rewrite div62_w_unsigned by assumption;reflexivity. Qed.

Lemma div62_inverse_cancellation f g k : Z.Odd f -> 1<=k ->
  (2^k | g+f*((modInv (-f) (2^k)*g) mod 2^k)).
Proof.
  intros Odd K;set (N:=2^k);set (v:=modInv (-f) N).
  assert (P : 1<N).
  { unfold N;pose proof (Z.pow_le_mono_r 2 1 k ltac:(lia) ltac:(lia));change (2^1) with 2 in *;lia. }
  assert (Opp : Z.Odd(-f)).
  { apply Z.odd_spec;rewrite Z.odd_opp;apply Z.odd_spec;exact Odd. }
  assert (Inv : ((-f)*v) mod N=1).
  { unfold v,N;rewrite modInv_mul_r,div62_odd_gcd_power by (assumption || lia).
    apply Z.mod_small;unfold N in P;lia. }
  pose proof (Z.div_mod ((-f)*v) N ltac:(lia)) as DI;rewrite Inv in DI.
  pose proof (Z.div_mod (v*g) N ltac:(lia)) as DW.
  exists (-(((-f)*v)/N)*g-f*((v*g)/N)).
  fold N v;replace ((v*g) mod N) with (v*g-N*((v*g)/N)) by lia.
  replace (g+f*(v*g-N*((v*g)/N))) with ((1+f*v)*g-f*N*((v*g)/N)) by ring.
  replace (1+f*v) with (-N*(((-f)*v)/N)) by lia;ring.
Qed.

Theorem div62_cancellation neg eta i f g : 0<=eta<=745 -> 1<=i<=62 -> Z.Odd f ->
  let k:=div62_cancel_bits neg eta i in
  let w:=Int.unsigned (div62_w_word neg (Int64.repr f) (Int64.repr g) (div62_mask neg eta i)) in
  0<=w<2^k /\ (2^k | g+f*w) /\
  Int64.and (Int64.add (Int64.repr g)
    (Int64.mul (Int64.repr f) (div62_w_long neg (Int64.repr f) (Int64.repr g) (div62_mask neg eta i))))
    (div62_mask neg eta i)=Int64.zero.
Proof.
  intros B I Odd;cbn zeta.
  pose proof (div62_cancel_bits_bound neg eta i B I) as KB.
  assert (K : 1<=div62_cancel_bits neg eta i<=6) by (destruct neg;lia).
  rewrite div62_w_unsigned,div62_w_long_value,div62_mask_value by assumption.
  split;[apply Z.mod_pos_bound;apply Z.pow_pos_nonneg;lia|].
  pose proof (div62_inverse_cancellation f g (div62_cancel_bits neg eta i) Odd ltac:(lia)) as Divides.
  split;[exact Divides|].
  rewrite div62_repr_mul,div62_repr_add,div62_repr_and,Z.land_ones by lia.
  assert (Zero : (g+f*((modInv (-f) (2^div62_cancel_bits neg eta i)*g) mod 2^div62_cancel_bits neg eta i))
    mod 2^div62_cancel_bits neg eta i=0) by (apply Zdivide_mod;exact Divides).
  rewrite Zero;reflexivity.
Qed.

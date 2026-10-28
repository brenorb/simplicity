(** Small integer-polynomial operations for checked finite-field certificates.
    Coefficients are untrusted data. The evaluation lemmas, followed by closed
    certificate equalities, will justify their use in the original table calls.
    No jet coverage or table nondegeneracy is asserted by this module. *)
From Coq Require Import ZArith List Lia Ring.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint polynomial_value (p:list Z) (x:Z) : Z :=
 match p with []=>0 | a::tail=>a+x*polynomial_value tail x end.

Fixpoint polynomial_trim (p:list Z) : list Z :=
 match p with
 | []=>[]
 | a::tail=>let rest:=polynomial_trim tail in
   match rest with []=>if Z.eqb a 0 then [] else [a] | _=>a::rest end
 end.

Lemma polynomial_trim_value p x :
 polynomial_value (polynomial_trim p) x=polynomial_value p x.
Proof.
 induction p as [|a tail IH];[reflexivity|].
 cbn [polynomial_trim].
 destruct (polynomial_trim tail) as [|b rest] eqn:Tail.
 - destruct (Z.eqb a 0) eqn:Zero;cbn [polynomial_value] in *.
   + apply Z.eqb_eq in Zero;subst a;rewrite <-IH;ring.
   + rewrite <-IH;ring.
 - cbn [polynomial_value] in *;rewrite IH;reflexivity.
Qed.

Fixpoint polynomial_add (modulus:Z) (p q:list Z) : list Z :=
 polynomial_trim
 (match p,q with
  | [],_=>q | _,[]=>p
  | a::tail,b::rest=>((a+b) mod modulus)::polynomial_add modulus tail rest
  end).

Definition polynomial_scale modulus k p :=
 polynomial_trim (map (fun a=>k*a mod modulus) p).
Definition polynomial_sub modulus p q :=
 polynomial_add modulus p (polynomial_scale modulus (-1) q).
Definition polynomial_shift (n:nat) (p:list Z) := repeat 0 n++p.

Fixpoint polynomial_mul modulus (p q:list Z) : list Z :=
 match p with
 | []=>[]
 | a::tail=>polynomial_add modulus (polynomial_scale modulus a q)
   (0::polynomial_mul modulus tail q)
 end.

Lemma polynomial_add_value modulus p q x : modulus<>0 ->
 polynomial_value (polynomial_add modulus p q) x mod modulus=
 (polynomial_value p x+polynomial_value q x) mod modulus.
Proof.
 intro Nonzero;revert q;induction p as [|a tail IH];intros [|b rest].
 - reflexivity.
 - cbn [polynomial_add];rewrite polynomial_trim_value;reflexivity.
 - cbn [polynomial_add];rewrite polynomial_trim_value;cbn [polynomial_value].
   rewrite Z.add_0_r;reflexivity.
 - change (polynomial_value
    (polynomial_trim (((a+b) mod modulus)::polynomial_add modulus tail rest)) x mod modulus=
    ((a+x*polynomial_value tail x)+(b+x*polynomial_value rest x)) mod modulus).
   rewrite polynomial_trim_value;cbn [polynomial_value].
   rewrite (Z.add_mod ((a+b) mod modulus)) by exact Nonzero.
   rewrite Z.mod_mod,(Z.mul_mod x),IH by exact Nonzero.
   rewrite <-Z.mul_mod,<-Z.add_mod by exact Nonzero.
   f_equal;ring.
Qed.

Lemma polynomial_scale_value modulus k p x : modulus<>0 ->
 polynomial_value (polynomial_scale modulus k p) x mod modulus=
 (k*polynomial_value p x) mod modulus.
Proof.
 intro Nonzero;unfold polynomial_scale;rewrite polynomial_trim_value.
 induction p as [|a tail IH];[cbn [map polynomial_value];rewrite Z.mul_0_r;reflexivity|].
 cbn [map polynomial_value].
 rewrite (Z.add_mod ((k*a) mod modulus)) by exact Nonzero.
 rewrite Z.mod_mod,(Z.mul_mod x),IH by exact Nonzero.
 rewrite <-Z.mul_mod,<-Z.add_mod by exact Nonzero.
 f_equal;ring.
Qed.

Lemma polynomial_sub_value modulus p q x : modulus<>0 ->
 polynomial_value (polynomial_sub modulus p q) x mod modulus=
 (polynomial_value p x-polynomial_value q x) mod modulus.
Proof.
 intro Nonzero;unfold polynomial_sub;rewrite polynomial_add_value by exact Nonzero.
 rewrite Z.add_mod,polynomial_scale_value by exact Nonzero.
 rewrite <-Z.add_mod by exact Nonzero;f_equal;ring.
Qed.

Lemma polynomial_shift_value n p x :
 polynomial_value (polynomial_shift n p) x=x^Z.of_nat n*polynomial_value p x.
Proof.
 induction n as [|n IH].
 - cbn [polynomial_shift repeat app];rewrite Z.mul_1_l;reflexivity.
 - change (0+x*polynomial_value (polynomial_shift n p) x=
    x^Z.of_nat (S n)*polynomial_value p x).
   rewrite IH,Nat2Z.inj_succ,Z.pow_succ_r by lia;ring.
Qed.

Lemma polynomial_mul_value modulus p q x : modulus<>0 ->
 polynomial_value (polynomial_mul modulus p q) x mod modulus=
 (polynomial_value p x*polynomial_value q x) mod modulus.
Proof.
 intro Nonzero;induction p as [|a tail IH].
 - cbn [polynomial_mul polynomial_value];reflexivity.
 - cbn [polynomial_mul];rewrite polynomial_add_value by exact Nonzero.
   rewrite Z.add_mod,polynomial_scale_value by exact Nonzero.
   cbn [polynomial_value].
   rewrite Z.add_0_l.
   rewrite (Z.mul_mod x (polynomial_value (polynomial_mul modulus tail q) x)),IH by exact Nonzero.
   rewrite <-Z.mul_mod,<-Z.add_mod by exact Nonzero.
   f_equal;ring.
Qed.

Lemma polynomial_mul_value_congruent modulus p q x a b : modulus<>0 ->
 polynomial_value p x mod modulus=a mod modulus ->
 polynomial_value q x mod modulus=b mod modulus ->
 polynomial_value (polynomial_mul modulus p q) x mod modulus=(a*b) mod modulus.
Proof.
 intros Nonzero Left Right;rewrite polynomial_mul_value,Z.mul_mod,Left,Right by exact Nonzero.
 rewrite <-Z.mul_mod by exact Nonzero;reflexivity.
Qed.

(** This reduction subtracts a multiple of q. Correct evaluation at a root
    needs no degree or monicity invariant. The concrete monic certificates
    make the structural Horner computation produce bounded remainders. *)
Definition polynomial_reduce modulus (p q:list Z) :=
 if Nat.ltb (length p) (length q) then polynomial_trim p else
 polynomial_sub modulus p
  (polynomial_scale modulus (last p 0)
   (polynomial_shift (length p-length q) q)).

Fixpoint polynomial_remainder modulus (p q:list Z) : list Z :=
 match p with
 | []=>[]
 | a::tail=>polynomial_reduce modulus (a::polynomial_remainder modulus tail q) q
 end.

Lemma polynomial_reduce_value modulus p q x : modulus<>0 ->
 polynomial_value q x mod modulus=0 ->
 polynomial_value (polynomial_reduce modulus p q) x mod modulus=
 polynomial_value p x mod modulus.
Proof.
 intros Nonzero Root;unfold polynomial_reduce.
 destruct (Nat.ltb (length p) (length q));[rewrite polynomial_trim_value;reflexivity|].
 assert (Zero:polynomial_value
   (polynomial_scale modulus (last p 0) (polynomial_shift (length p-length q) q)) x mod modulus=0).
 { rewrite polynomial_scale_value,polynomial_shift_value by exact Nonzero.
   rewrite (Z.mul_mod (last p 0)),(Z.mul_mod (x^Z.of_nat (length p-length q))),Root by exact Nonzero.
   rewrite !Z.mul_0_r,!Z.mod_0_l by exact Nonzero;reflexivity. }
 rewrite polynomial_sub_value,Zminus_mod,Zero,Z.sub_0_r,Z.mod_mod by exact Nonzero.
 reflexivity.
Qed.

Lemma polynomial_remainder_value modulus p q x : modulus<>0 ->
 polynomial_value q x mod modulus=0 ->
 polynomial_value (polynomial_remainder modulus p q) x mod modulus=
 polynomial_value p x mod modulus.
Proof.
 intros Nonzero Root;induction p as [|a tail IH];[reflexivity|].
 cbn [polynomial_remainder];rewrite polynomial_reduce_value by assumption.
 cbn [polynomial_value].
 rewrite (Z.add_mod a),(Z.mul_mod x),IH by exact Nonzero.
 rewrite <-Z.mul_mod,<-Z.add_mod by exact Nonzero;reflexivity.
Qed.

Fixpoint polynomial_power modulus (base:list Z) (exponent:positive) (q:list Z) : list Z :=
 match exponent with
 | xH=>polynomial_remainder modulus base q
 | xO n=>let r:=polynomial_power modulus base n q in
   polynomial_remainder modulus (polynomial_mul modulus r r) q
 | xI n=>let r:=polynomial_power modulus base n q in
   polynomial_remainder modulus (polynomial_mul modulus (polynomial_mul modulus r r) base) q
 end.

Theorem polynomial_power_value modulus base exponent q x : modulus<>0 ->
 polynomial_value q x mod modulus=0 ->
 polynomial_value (polynomial_power modulus base exponent q) x mod modulus=
 (polynomial_value base x)^Z.pos exponent mod modulus.
Proof.
 intros Nonzero Root;induction exponent as [n IH|n IH|].
 - cbn [polynomial_power];rewrite polynomial_remainder_value by assumption.
   transitivity ((((polynomial_value base x)^Z.pos n*(polynomial_value base x)^Z.pos n)*
    polynomial_value base x) mod modulus).
   + apply polynomial_mul_value_congruent;[exact Nonzero| |reflexivity].
     apply polynomial_mul_value_congruent;assumption.
   + f_equal;replace (Z.pos (xI n)) with (Z.pos n+Z.pos n+1) by lia.
     rewrite !Z.pow_add_r,Z.pow_1_r by lia;ring.
 - cbn [polynomial_power];rewrite polynomial_remainder_value by assumption.
   transitivity (((polynomial_value base x)^Z.pos n*(polynomial_value base x)^Z.pos n) mod modulus).
   + apply polynomial_mul_value_congruent;assumption.
   + f_equal;replace (Z.pos (xO n)) with (Z.pos n+Z.pos n) by lia.
     rewrite Z.pow_add_r by lia;reflexivity.
 - cbn [polynomial_power];rewrite Z.pow_1_r;apply polynomial_remainder_value;assumption.
Qed.

(** A computational refinement of the generic polynomial checker. Every
    operation is proved equal to the generic definition, without root or
    range assumptions. Only coefficient computation uses the fast reducer. *)
From Coq Require Import ZArith List.
Require Import C.jet_secp_fe_math C.jet_secp_fast_remainder C.jet_secp_polynomial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint fast_polynomial_add (p q:list Z) : list Z :=
 polynomial_trim
 (match p,q with
 | [],_=>q | _,[]=>p
 | a::tail,b::rest=>secp_coefficient_remainder (a+b)::fast_polynomial_add tail rest
 end).

Definition fast_polynomial_scale k p :=
 polynomial_trim (map (fun a=>secp_coefficient_remainder (k*a)) p).
Definition fast_polynomial_sub p q := fast_polynomial_add p (fast_polynomial_scale (-1) q).

Fixpoint fast_polynomial_mul (p q:list Z) : list Z :=
 match p with []=>[] | a::tail=>fast_polynomial_add (fast_polynomial_scale a q)
  (0::fast_polynomial_mul tail q) end.

Definition fast_polynomial_reduce (p q:list Z) :=
 if Nat.ltb (length p) (length q) then polynomial_trim p else
 fast_polynomial_sub p
  (fast_polynomial_scale (last p 0) (polynomial_shift (length p-length q) q)).

Fixpoint fast_polynomial_remainder (p q:list Z) : list Z :=
 match p with []=>[] | a::tail=>fast_polynomial_reduce (a::fast_polynomial_remainder tail q) q end.

Fixpoint fast_polynomial_power (base:list Z) (exponent:positive) (q:list Z) : list Z :=
 match exponent with
 | xH=>fast_polynomial_remainder base q
 | xO n=>let r:=fast_polynomial_power base n q in
   fast_polynomial_remainder (fast_polynomial_mul r r) q
 | xI n=>let r:=fast_polynomial_power base n q in
   fast_polynomial_remainder (fast_polynomial_mul (fast_polynomial_mul r r) base) q
 end.

Lemma fast_polynomial_add_correct p q : fast_polynomial_add p q=polynomial_add feP p q.
Proof.
 revert q;induction p as [|a tail IH];intros [|b rest];try reflexivity.
 cbn [fast_polynomial_add polynomial_add];rewrite secp_coefficient_remainder_correct,IH;reflexivity.
Qed.

Lemma fast_polynomial_scale_correct k p : fast_polynomial_scale k p=polynomial_scale feP k p.
Proof.
 unfold fast_polynomial_scale,polynomial_scale;f_equal.
 induction p as [|a tail IH];[reflexivity|].
 cbn [map];rewrite secp_coefficient_remainder_correct,IH;reflexivity.
Qed.

Lemma fast_polynomial_sub_correct p q : fast_polynomial_sub p q=polynomial_sub feP p q.
Proof. unfold fast_polynomial_sub,polynomial_sub;rewrite fast_polynomial_add_correct,fast_polynomial_scale_correct;reflexivity. Qed.

Lemma fast_polynomial_mul_correct p q : fast_polynomial_mul p q=polynomial_mul feP p q.
Proof.
 induction p as [|a tail IH];[reflexivity|].
 cbn [fast_polynomial_mul polynomial_mul];rewrite fast_polynomial_add_correct,fast_polynomial_scale_correct,IH;reflexivity.
Qed.

Lemma fast_polynomial_reduce_correct p q : fast_polynomial_reduce p q=polynomial_reduce feP p q.
Proof.
 unfold fast_polynomial_reduce,polynomial_reduce.
 destruct (Nat.ltb (length p) (length q));[reflexivity|].
 rewrite fast_polynomial_sub_correct,fast_polynomial_scale_correct;reflexivity.
Qed.

Lemma fast_polynomial_remainder_correct p q : fast_polynomial_remainder p q=polynomial_remainder feP p q.
Proof.
 induction p as [|a tail IH];[reflexivity|].
 cbn [fast_polynomial_remainder polynomial_remainder];rewrite fast_polynomial_reduce_correct,IH;reflexivity.
Qed.

Theorem fast_polynomial_power_correct base exponent q :
 fast_polynomial_power base exponent q=polynomial_power feP base exponent q.
Proof.
 induction exponent as [n IH|n IH|];cbn [fast_polynomial_power polynomial_power];
 rewrite fast_polynomial_remainder_correct,?fast_polynomial_mul_correct,?fast_polynomial_mul_correct,?IH;reflexivity.
Qed.

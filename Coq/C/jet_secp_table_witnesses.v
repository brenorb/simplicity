(** Pure evaluation bridge for compressed coefficient witnesses. *)
From Coq Require Import ZArith List Lia Ring.
Require Import C.jet_secp_fe_math C.jet_secp_polynomial C.jet_secp_fast_polynomial
 C.jet_secp_field_prime.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Fixpoint table_cubic_coefficients (q:list Z) : list Z :=
 match q with []=>[] | a::tail=>a::0::0::table_cubic_coefficients tail end.
Definition table_cubic_expand q := polynomial_trim (table_cubic_coefficients q).
Lemma table_cubic_coefficients_value q x :
 polynomial_value (table_cubic_coefficients q) x=polynomial_value q (x*x*x).
Proof.
 induction q as [|a tail IH];[reflexivity|].
 cbn [table_cubic_coefficients polynomial_value];rewrite IH;ring.
Qed.
Lemma table_cubic_expand_value q x :
 polynomial_value (table_cubic_expand q) x=polynomial_value q (x*x*x).
Proof. unfold table_cubic_expand;rewrite polynomial_trim_value;apply table_cubic_coefficients_value. Qed.
Definition table_odd_witness (n:Z) (needs_x:bool) (q:list Z) := fast_polynomial_scale n
 (if needs_x then polynomial_shift 1 (table_cubic_expand q) else table_cubic_expand q).
Lemma table_odd_witness_value n needs_x q x :
 polynomial_value (table_odd_witness n needs_x q) x mod feP=
 (n*(if needs_x then x else 1)*polynomial_value q (x*x*x)) mod feP.
Proof.
 unfold table_odd_witness;rewrite fast_polynomial_scale_correct,polynomial_scale_value
   by (unfold feP,feR;lia).
 destruct needs_x.
 - rewrite polynomial_shift_value,table_cubic_expand_value.
   change ((n*(x^1*polynomial_value q (x*x*x))) mod feP=
     (n*x*polynomial_value q (x*x*x)) mod feP).
   rewrite Z.pow_1_r;f_equal;ring.
 - rewrite table_cubic_expand_value;f_equal;ring.
Qed.
Lemma table_odd_witness_nonzero n needs_x q x :
 n mod feP<>0 -> x mod feP<>0 -> polynomial_value q (x*x*x) mod feP<>0 ->
 polynomial_value (table_odd_witness n needs_x q) x mod feP<>0.
Proof.
 intros N X Q;rewrite table_odd_witness_value.
 apply secp256k1_nonzero_product;[|exact Q].
 apply secp256k1_nonzero_product;[exact N|].
 destruct needs_x;[exact X|vm_compute;discriminate].
Qed.

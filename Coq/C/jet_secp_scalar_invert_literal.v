(** Faithful scalar_invert program from frozen LibSecp256k1.hs:590. Reuse
    the word-exact Bezout simulation and its proved termination, rather than
    substituting a mathematical inverse for the literal program. This bridge
    is used to interpret the actual scalar inverse finishing execution. *)
From Coq Require Import ZArith Znumtheory Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_secp_canonical_scalar
 C.jet_secp_canonical_scalar_negate C.jet_secp_eea_literal C.jet_secp_eea_numeric
 C.jet_secp_eea_fast C.jet_secp_invert_literal C.jet_secp_invert_modinv
 C.jet_secp_scalar_prime C.modinv.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Opaque literal_bezout canonical_scalar_negate canonical_group_word.

Definition literal_scalar_invert {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
 @literal_inverse_body (Word 8) term canonical_group_word
   (@literal_bezout 8 term) (@canonical_scalar_negate term).
Definition literal_scalar_invert_numeric x :=
 eea_selected_inverse canonical_group_order
   (eea_run_numeric (2^256) 512 (((1,0),canonical_group_order),((0,1),x))).

Theorem literal_scalar_invert_numeric_step (x : Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) (@literal_scalar_invert Alg.CoreFunSem x)=
 literal_scalar_invert_numeric (@toZ (WordToZ 8) x).
Proof.
 unfold literal_scalar_invert;rewrite literal_inverse_body_fun.
 pose proof (literal_bezout_numeric 8 canonical_group_word x) as Bezout.
 rewrite canonical_group_word_value,eea_word_modulus256 in Bezout.
 change (Nat.pow 2 (S 8)) with 512%nat in Bezout.
 unfold literal_scalar_invert_numeric,eea_selected_inverse;rewrite <-Bezout.
 destruct (@literal_bezout 8 Alg.CoreFunSem (canonical_group_word,x)) as [[a b] | [d e]].
 - unfold inverse_select;cbn [eea_bezout_denote];rewrite canonical_scalar_negate_numeric.
   replace (canonical_group_order-@toZ (WordToZ 8) b) with
     (-@toZ (WordToZ 8) b+1*canonical_group_order) by ring.
   rewrite Z_mod_plus_full;reflexivity.
 - reflexivity.
Qed.

Theorem literal_scalar_invert_word (x : Ty.tySem (Word 8)) :
 @literal_scalar_invert Alg.CoreFunSem x=
 @fromZ (WordToZ 8) (literal_scalar_invert_numeric (@toZ (WordToZ 8) x)).
Proof.
 rewrite <-(from_toZ (@literal_scalar_invert Alg.CoreFunSem x)) at 1.
 rewrite literal_scalar_invert_numeric_step;reflexivity.
Qed.

(** Early stopping is a proved fixed-point optimization of this same
    literal EEA, used only to check the zero and modulus inputs cheaply. *)
Definition literal_scalar_invert_fast x :=
 eea_selected_inverse canonical_group_order
   (eea_run_fast (2^256) 512 (((1,0),canonical_group_order),((0,1),x))).
Lemma literal_scalar_invert_fast_matches x : 0<=x ->
 literal_scalar_invert_fast x=literal_scalar_invert_numeric x.
Proof.
 intro X;unfold literal_scalar_invert_fast,literal_scalar_invert_numeric.
 rewrite eea_run_fast_matches;[reflexivity|vm_compute;reflexivity|].
 unfold eea_state_valid,eea_row_valid;cbn [fst snd].
 pose proof canonical_group_order_range;change (word_modulus 8) with (2^256) in *.
 repeat split;lia.
Qed.
Lemma literal_scalar_invert_numeric_zero : literal_scalar_invert_numeric 0=0.
Proof. rewrite <-literal_scalar_invert_fast_matches by lia;vm_compute;reflexivity. Qed.
Lemma literal_scalar_invert_numeric_order : literal_scalar_invert_numeric canonical_group_order=0.
Proof.
 rewrite <-literal_scalar_invert_fast_matches by (unfold canonical_group_order;lia).
 vm_compute;reflexivity.
Qed.

Lemma scalar_gcd_nonmultiple z : 0<z<2*canonical_group_order -> z<>canonical_group_order ->
 Z.gcd canonical_group_order z=1.
Proof.
 intros Range Nonmultiple;apply Zgcd_1_rel_prime;apply prime_rel_prime;[apply secp256k1_scalar_prime|].
 intros [q Multiple];assert(q=1) by (unfold canonical_group_order in *;nia).
 subst q;apply Nonmultiple;nia.
Qed.

Theorem literal_scalar_invert_numeric_inverse z : 0<z<2^256 -> z<>canonical_group_order ->
 0<=literal_scalar_invert_numeric z<canonical_group_order /\
 (literal_scalar_invert_numeric z*z) mod canonical_group_order=1.
Proof.
 intros Range Nonmultiple.
 assert (Size : 1<canonical_group_order<2^256 /\ 2^256<2*canonical_group_order)
   by (unfold canonical_group_order;lia).
 pose proof (eea_run_inverse (2^256) 256 canonical_group_order z ltac:(lia)
   Range ltac:(lia) ltac:(change(Z.of_nat 256) with 256;lia)
   (scalar_gcd_nonmultiple z ltac:(lia) Nonmultiple)) as Inverse.
 change (2*256)%nat with 512%nat in Inverse;exact Inverse.
Qed.

Theorem literal_scalar_invert_numeric_modInv z : 0<=z<2^256 ->
 literal_scalar_invert_numeric z=modInv z canonical_group_order.
Proof.
 intros Range;destruct(Z.eq_dec z 0) as [Zero|Nonzero].
 - subst z;rewrite literal_scalar_invert_numeric_zero,modInv_zero;reflexivity.
 - destruct(Z.eq_dec z canonical_group_order) as [Order|Nonmultiple].
   + subst z;rewrite literal_scalar_invert_numeric_order,modInv_divide by apply Z.divide_refl;reflexivity.
   + destruct(literal_scalar_invert_numeric_inverse z ltac:(lia) Nonmultiple) as (Bounds & Product).
     pose proof(modInv_mul_unique_l z canonical_group_order (literal_scalar_invert_numeric z) Product) as Unique.
     rewrite Z.mod_small in Unique by exact Bounds;exact Unique.
Qed.

Theorem literal_scalar_invert_modInv (word : Ty.tySem (Word 8)) :
 @literal_scalar_invert Alg.CoreFunSem word=
 @fromZ (WordToZ 8) (modInv (@toZ (WordToZ 8) word) canonical_group_order).
Proof.
 rewrite literal_scalar_invert_word,literal_scalar_invert_numeric_modInv;[reflexivity|].
 exact(word_value_bounds 8 word).
Qed.

(** The literal EEA's selected coefficient, not an assumed mathematical
    inverse. The run theorem discharges all intermediate-state premises. *)
From Coq Require Import ZArith Znumtheory Lia.
Require Import C.jet_secp_eea_numeric C.jet_secp_eea_fast
 C.jet_secp_eea_coefficients C.jet_secp_eea_remainders
 C.jet_secp_canonical_normalize C.jet_secp_fe_math C.jet_secp_field_prime
 C.jet_secp_invert_literal C.modinv C.jet_predicate_spec C.jet_toZ.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eea_selected_inverse p s :=
 match eea_bezout_numeric s with
 | inl (_,b) => (p-b) mod p
 | inr (_,e) => e
 end.

Lemma eea_finished_inverse p z s : 1<p -> eea_coefficients p z s ->
 eea_remainder_gcd s=1 -> eea_finished s=Datatypes.true ->
 0<=eea_selected_inverse p s<p /\ (eea_selected_inverse p s*z) mod p=1.
Proof.
 destruct s as [[[a b] c] [[d e] f]].
 intros P (A & B & D & E & C & F & Left & Right & SumZ & SumP) Gcd Finished.
 change (Z.gcd c f=1) in Gcd.
 change (orb (Z.eqb c 0) (Z.eqb f 0)=Datatypes.true) in Finished.
 unfold eea_selected_inverse,eea_bezout_numeric.
 destruct (Z.eqb_spec f 0) as [ZeroF|NonzeroF].
 - subst f;rewrite Z.gcd_0_r,Z.abs_eq in Gcd by lia;subst c.
   split;[apply Z.mod_pos_bound;lia|].
   rewrite Z.mul_mod_idemp_l by lia.
   replace ((p-b)*z) with (1+(z-a)*p) by nia.
   rewrite Z.mod_add by lia;apply Z.mod_small;lia.
 - assert (ZeroC : c=0) by (rewrite Bool.orb_false_r in Finished;apply Z.eqb_eq;exact Finished).
   rewrite ZeroC,Z.gcd_0_l,Z.abs_eq in Gcd by lia;subst f.
   assert (e<>p).
   { intro Equal;subst e;destruct (Z_le_dec z d);nia. }
   split;[lia|].
   replace (e*z) with (1+d*p) by nia.
   rewrite Z.mod_add by lia;apply Z.mod_small;lia.
Qed.

Theorem eea_run_inverse modulus bits p z :
 1<p -> 0<z<modulus -> p<modulus -> p<2^Z.of_nat bits -> Z.gcd p z=1 ->
 let result:=eea_run_numeric modulus (2*bits) (((1,0),p),((0,1),z)) in
 0<=eea_selected_inverse p result<p /\ (eea_selected_inverse p result*z) mod p=1.
Proof.
 intros P ZRange Modulus Capacity Coprime;cbn zeta.
 apply eea_finished_inverse;[exact P| | |].
 - apply eea_coefficients_run;[lia|lia|apply eea_coefficients_initial;lia].
 - rewrite eea_remainder_run_gcd;exact Coprime.
 - apply eea_run_finishes.
   + unfold eea_remainders_nonnegative,eea_remainders;cbn [fst snd];lia.
   + unfold eea_minimum,eea_pair_min,eea_remainders;cbn [fst snd].
     pose proof (Z.le_min_l p z);lia.
Qed.

Lemma field_gcd_nonmultiple z : 0<z<2*feP -> z<>feP -> Z.gcd feP z=1.
Proof.
 intros Range Nonmultiple;apply Zgcd_1_rel_prime;apply prime_rel_prime;[apply secp256k1_field_prime|].
 intros [q Multiple].
 assert (q=1) by (unfold feP,feR in *;nia).
 subst q;apply Nonmultiple;nia.
Qed.

Theorem literal_invert_numeric_inverse z :
 0<z<2^256 -> z<>feP ->
 0<=literal_invert_numeric z<feP /\ (literal_invert_numeric z*z) mod feP=1.
Proof.
 intros Range Nonmultiple.
 pose proof (eea_run_inverse (2^256) 256 feP z ltac:(unfold feP,feR;lia)
   Range ltac:(unfold feP,feR;lia) ltac:(change (Z.of_nat 256) with 256;unfold feP,feR;lia)
   (field_gcd_nonmultiple z ltac:(unfold feP,feR in *;lia) Nonmultiple)) as Inverse.
 change (2*256)%nat with 512%nat in Inverse.
 unfold literal_invert_numeric;rewrite canonical_field_order_matches_limb_model.
 exact Inverse.
Qed.

Lemma literal_invert_numeric_field_order : literal_invert_numeric feP=0.
Proof.
 rewrite <-literal_invert_fast_matches by (unfold feP,feR;lia).
 vm_compute;reflexivity.
Qed.

Theorem literal_invert_numeric_modInv z : 0<=z<2^256 -> literal_invert_numeric z=modInv z feP.
Proof.
 intros Range;destruct (Z.eq_dec z 0) as [Zero|Nonzero].
 - subst z;rewrite literal_invert_numeric_zero,modInv_zero;reflexivity.
 - destruct (Z.eq_dec z feP) as [Order|Nonmultiple].
   + subst z;rewrite literal_invert_numeric_field_order,modInv_divide by apply Z.divide_refl;reflexivity.
   + destruct (literal_invert_numeric_inverse z ltac:(lia) Nonmultiple) as [Bounds Product].
     pose proof (modInv_mul_unique_l z feP (literal_invert_numeric z) Product) as Unique.
     rewrite Z.mod_small in Unique by exact Bounds;exact Unique.
Qed.

Theorem literal_fe_invert_modInv (word : Ty.tySem (Word 8)) :
 @literal_fe_invert Alg.CoreFunSem word=
 @fromZ (WordToZ 8) (modInv (@toZ (WordToZ 8) word) feP).
Proof.
 rewrite literal_fe_invert_word,literal_invert_numeric_modInv;[reflexivity|].
 exact (word_value_bounds 8 word).
Qed.

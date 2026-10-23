(** A checked normalization certificate for the exact literal generator:
    verify rescaled coordinates instead of evaluating Bezout at each leaf.
    No inverse or generator-table premise is assumed by the checker. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_invert_modinv C.jet_secp_fe_math C.jet_secp_invert_literal
 C.jet_secp_eea_fast C.jet_secp_generate_numeric C.jet_secp_gej_norm_literal C.jet_toZ C.jet_predicate_spec.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma inverse_coordinate_cancel p z v x t : p<>0 ->
 (v*z) mod p=1 -> (t*z) mod p=x mod p -> (x*v) mod p=t mod p.
Proof.
 intros P Inverse Rescaled.
 rewrite (Z.mul_mod x v p),<-Rescaled,<-Z.mul_mod by exact P.
 replace (t*z*v) with (t*(v*z)) by ring.
 rewrite (Z.mul_mod t (v*z) p),Inverse,Z.mul_1_r,Z.mod_mod by exact P;reflexivity.
Qed.

Theorem literal_norm_fast_rescaled x y z tx ty :
 0<=z<2^256 -> z mod feP<>0 -> 0<=tx<feP -> 0<=ty<feP ->
 (tx*z*z) mod feP=x mod feP -> (ty*z*z*z) mod feP=y mod feP ->
 literal_norm_fast ((x,y),z)=(tx,ty).
Proof.
 intros ZRange Nonzero TX TY X Y.
 assert (ZPositive : 0<z).
 { destruct (Z.eq_dec z 0) as [Zero|Positive];[subst z;contradiction Nonzero;reflexivity|lia]. }
 assert (Nonmultiple : z<>feP).
 { intro Same;subst z;apply Nonzero;apply Z.mod_same;unfold feP,feR;lia. }
 destruct (literal_invert_numeric_inverse z ltac:(lia) Nonmultiple) as [Bounds Inverse].
 assert (P : feP<>0) by (unfold feP,feR;lia).
 pose proof (inverse_coordinate_cancel feP z (literal_invert_numeric z) x (tx*z) P Inverse X) as X1.
 pose proof (inverse_coordinate_cancel feP z (literal_invert_numeric z)
   (x*literal_invert_numeric z) tx P Inverse (eq_sym X1)) as X2.
 pose proof (inverse_coordinate_cancel feP z (literal_invert_numeric z) y (ty*z*z) P Inverse Y) as Y1.
 pose proof (inverse_coordinate_cancel feP z (literal_invert_numeric z)
   (y*literal_invert_numeric z) (ty*z) P Inverse (eq_sym Y1)) as Y2.
 pose proof (inverse_coordinate_cancel feP z (literal_invert_numeric z)
   (y*literal_invert_numeric z*literal_invert_numeric z) ty P Inverse (eq_sym Y2)) as Y3.
 unfold literal_norm_fast;rewrite literal_invert_fast_matches by lia.
 rewrite X2,Y3,!Z.mod_small by assumption;reflexivity.
Qed.

Definition generator_normalization_check x y z tx ty :=
 andb (0<=?z) (andb (z<?2^256) (andb (negb (Z.eqb (z mod feP) 0))
 (andb (0<=?tx) (andb (tx<?feP) (andb (0<=?ty) (andb (ty<?feP)
 (andb (Z.eqb ((tx*z*z) mod feP) (x mod feP))
       (Z.eqb ((ty*z*z*z) mod feP) (y mod feP))))))))).

Theorem generator_normalization_check_sound x y z tx ty :
 generator_normalization_check x y z tx ty=Datatypes.true -> literal_norm_fast ((x,y),z)=(tx,ty).
Proof.
 unfold generator_normalization_check;rewrite !Bool.andb_true_iff.
 intros (Z0 & ZM & NZ & TX0 & TXP & TY0 & TYP & X & Y).
 apply Z.leb_le in Z0,TX0,TY0;apply Z.ltb_lt in ZM,TXP,TYP.
 apply Bool.negb_true_iff in NZ;apply Z.eqb_neq in NZ.
 apply Z.eqb_eq in X,Y;apply literal_norm_fast_rescaled;try assumption;lia.
Qed.

Theorem literal_gej_norm_fast_word (x y z : Ty.tySem (Word 8)) :
 @literal_gej_norm Alg.CoreFunSem ((x,y),z)=
 (@fromZ (WordToZ 8) (fst (literal_norm_fast (@toZ (WordToZ 8) x,@toZ (WordToZ 8) y,@toZ (WordToZ 8) z))),
  @fromZ (WordToZ 8) (snd (literal_norm_fast (@toZ (WordToZ 8) x,@toZ (WordToZ 8) y,@toZ (WordToZ 8) z)))).
Proof.
 rewrite literal_gej_norm_word;unfold literal_norm_fast,literal_gej_norm_numeric_value.
 rewrite literal_invert_fast_matches by (pose proof (word_value_bounds 8 z);lia);reflexivity.
Qed.

Theorem generator_normalization_check_literal (x y z : Ty.tySem (Word 8)) tx ty :
 generator_normalization_check (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z) tx ty=Datatypes.true ->
 @literal_gej_norm Alg.CoreFunSem ((x,y),z)=(@fromZ (WordToZ 8) tx,@fromZ (WordToZ 8) ty).
Proof. intro Check;rewrite literal_gej_norm_fast_word,(generator_normalization_check_sound _ _ _ _ _ Check);reflexivity. Qed.

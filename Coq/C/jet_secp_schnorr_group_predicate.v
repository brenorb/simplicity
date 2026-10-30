(** The two signature-verifier point predicates agree; C lifecycle is separate. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_predicate_spec C.jet_word_repr C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_order C.jet_secp_curve_group_scalar_sign C.jet_secp_lookup5_group
 C.jet_secp_signed_group_action C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_negate
 C.jet_secp_scalar_prime C.jet_secp_affine_word_valid C.jet_secp_even_x_test
 C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group C.jet_secp_linear_check_group
 C.jet_secp_linear_combination_group C.jet_secp_strauss_complete_program
 C.jet_secp_literal_add_program C.jet_secp_gej_negate_literal C.jet_secp_curve_literal
 C.jet_secp_decompress_literal C.jet_secp_decompress_sign C.jet_secp_point_verify_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_scalar_normalize canonical_scalar_negate literal_off_curve_linear_combination_1
 literal_decompress literal_point_check literal_ge_negate secp_group_signed_power SMain.add SMain.opp.
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Lemma secp_scalar_normalize_idempotent (raw:Ty.tySem (Word 8)):
 @canonical_scalar_normalize Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw)=
 @canonical_scalar_normalize Alg.CoreFunSem raw.
Proof.
 apply (toZ_injective (WordToZ 8));rewrite !canonical_scalar_normalize_numeric.
 apply Z.mod_mod;pose proof secp_scalar_order_positive;lia.
Qed.
Lemma secp_schnorr_scalar_sign (p:secp_group_point) (raw:Ty.tySem (Word 8)):
 secp_group_signed_power p
 (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem
  (@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw))))=
 secp_group_signed_power (SMain.opp secp_group_theory p)
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)).
Proof.
 rewrite !secp_group_signed_power_nonnegative by (apply (proj1 (word_value_bounds 8 _))).
 assert (NormalizeNeg:@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem
  (@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw)))=
  @toZ (WordToZ 8) (@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw))).
 { rewrite canonical_scalar_normalize_numeric,!canonical_scalar_negate_numeric.
   apply Z.mod_mod;pose proof secp_scalar_order_positive;lia. }
 rewrite NormalizeNeg;apply secp_group_normalized_scalar_sign.
Qed.
Theorem secp_schnorr_point_predicate (pk raw s r ax ay:Ty.tySem (Word 8)):
 @literal_decompress Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 0<=@toZ (WordToZ 8) r<feP ->
 Bit.toBool (@literal_point_check Alg.CoreFunSem
  (((@canonical_scalar_normalize Alg.CoreFunSem raw,(inr tt,pk)),s),(inl tt,r)))=
 secp_even_x_test (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
  ((@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw),
    ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),s)) r.
Proof.
 intros PublicKey RangeR.
 destruct (secp_decompress_represented pk (inl tt) ax ay PublicKey) as [p [RepP FiniteP]].
 pose proof (secp_decompress_curve pk (inl tt) (ax,ay) PublicKey) as CurveP.
 set (np:=@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw)).
 set (q:=secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem np))⊕
  secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem s))).
 pose proof (secp_literal_linear_combination_affine_group np s ax ay p CurveP RepP) as Result.
 fold np q in Result.
 pose proof (secp_affine_negate_group (GZnZ.one feP) (ax,ay) p RepP) as Negative.
 destruct (@literal_ge_negate Alg.CoreFunSem (ax,ay)) as [nax nay] eqn:Neg.
 pose proof (secp_affine_word_rep_curve nax nay _ Negative) as CurveNegative.
 assert (OddKey:@literal_decompress Alg.CoreFunSem (inr tt,pk)=inr (nax,nay)).
 { rewrite literal_decompress_opposite_parity,PublicKey,Neg;reflexivity. }
 assert (SameSum:
  secp_group_signed_power (SMain.opp secp_group_theory p)
   (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem raw)))⊕
  secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem s))=q).
 { unfold q,np;rewrite secp_scalar_normalize_idempotent,secp_schnorr_scalar_sign;reflexivity. }
 fold np.
 destruct (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
  ((np,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),s)) as [[cx cy] cz] eqn:Computed.
 apply Bool.eq_true_iff_eq.
 rewrite literal_point_check_value.
 rewrite (secp_even_x_test_group cx cy cz r q Result RangeR).
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,r)) as [u|decodedR] eqn:DecodeR.
 - destruct u;split;[discriminate|].
   intros (ux & uy & Contradiction & _);discriminate Contradiction.
 - destruct decodedR as [rx ry];rewrite OddKey.
   destruct (secp_decompress_represented r (inl tt) rx ry DecodeR) as [rp [RepR FiniteR]].
   pose proof (secp_decompress_curve r (inl tt) (rx,ry) DecodeR) as CurveR.
   rewrite (secp_literal_linear_check_group _ _ _ _ _ _ _ _ CurveNegative CurveR Negative RepR),SameSum.
   split.
   + intro Equal;exists rx,ry;split;[reflexivity|rewrite Equal;exact RepR].
   + intros (ux & uy & Decoded & RepSame).
     injection Decoded as <- <-.
     exact (secp_jacobian_word_rep_unique _ _ _ _ RepSame RepR).
Qed.

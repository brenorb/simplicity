(** Guarded BIP340 predicate, using the original verifier's sign convention.
    This is a pure composition result; the public C lifecycle is separate. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_predicate_spec C.jet_secp_fe_math C.jet_secp_canonical_normalize
 C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_negate C.jet_secp_literal_add_program
 C.jet_secp_even_x_test C.jet_secp_decompress_literal C.jet_secp_decompress_sign
 C.jet_secp_schnorr_group_predicate C.jet_secp_point_verify_literal C.jet_secp_strauss_complete_program
 C.jet_secp_schnorr_verify_literal C.jet_secp_schnorr_challenge_hash.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_point_check literal_decompress literal_bip0340_check canonical_scalar_normalize
 canonical_scalar_negate literal_off_curve_linear_combination_1 secp_even_x_test.
Definition secp_schnorr_check_test (pk msg r s:Ty.tySem (Word 8)):bool:=
 if @toZ (WordToZ 8) pk <? feP then
 if andb (@toZ (WordToZ 8) r <? feP) (@toZ (WordToZ 8) s <? canonical_group_order) then
 match @literal_decompress Alg.CoreFunSem (inl tt,pk) with
 |inl _=>Datatypes.false
 |inr ap=>secp_even_x_test (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
   ((@canonical_scalar_negate Alg.CoreFunSem (@canonical_scalar_normalize Alg.CoreFunSem
      (schnorr_challenge_hash_word r pk msg)),(ap,@literal_fe_one256 Alg.CoreFunSem tt)),s)) r
 end
 else Datatypes.false else Datatypes.false.
Lemma secp_schnorr_point_failed (pk raw s r:Ty.tySem (Word 8)):
 @literal_decompress Alg.CoreFunSem (inl tt,pk)=inl tt ->
 Bit.toBool (@literal_point_check Alg.CoreFunSem (((raw,(inr tt,pk)),s),(inl tt,r)))=Datatypes.false.
Proof.
 intro Failed;rewrite literal_point_check_value,literal_decompress_opposite_parity,Failed.
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,r)) as [u|ap];reflexivity.
Qed.
Theorem secp_schnorr_check_predicate (pk msg r s:Ty.tySem (Word 8)):
 Bit.toBool (@literal_bip0340_check Alg.CoreFunSem ((pk,msg),(r,s)))=
 secp_schnorr_check_test pk msg r s.
Proof.
 rewrite literal_bip0340_check_guarded_value;unfold secp_schnorr_check_test.
 rewrite canonical_field_order_matches_limb_model.
 destruct (@toZ (WordToZ 8) pk <? feP) eqn:PKRange;[|reflexivity].
 destruct (andb (@toZ (WordToZ 8) r <? feP) (@toZ (WordToZ 8) s <? canonical_group_order)) eqn:SignatureRange;
 [|reflexivity].
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,pk)) as [u|ap] eqn:Key.
 - destruct u;apply secp_schnorr_point_failed;exact Key.
 - destruct ap as [ax ay];apply secp_schnorr_point_predicate;[exact Key|].
   apply Bool.andb_true_iff in SignatureRange;destruct SignatureRange as [RBound _].
   apply Z.ltb_lt in RBound;pose proof (word_value_bounds 8 r);lia.
Qed.

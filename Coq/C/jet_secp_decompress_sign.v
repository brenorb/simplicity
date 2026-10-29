(** Parity convention bridge needed by the two signature verifiers. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_literal
 C.jet_secp_decompress_literal C.jet_secp_root_literal C.jet_secp_root_chain_numeric C.jet_secp_canonical_normalize
 C.jet_secp_negate_literal_contract C.jet_secp_write_ge_negated_literal
 C.jet_secp_square_execution C.jet_secp_rescale_literal C.jet_secp_literal_add_program C.jet_secp_canonical_zero C.jet_secp_canonical_odd C.jet_secp_gej_negate_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_square literal_fe_multiply literal_fe_tower literal_fe_add literal_fe_cube
 canonical_fe_is_zero canonical_fe_is_odd canonical_fe_normalize literal_fe_negate literal_ge_negate toZ.
Lemma decompress_root_candidate_range (x:Ty.tySem (Word 8)):0<=@toZ (WordToZ 8) (literal_root_candidate x)<feP.
Proof.
 unfold literal_root_candidate;rewrite literal_square_numeric.
 apply Z.mod_pos_bound;unfold feP,feR;lia.
Qed.
Local Opaque literal_root_candidate.
Lemma decompress_y_from_x_range (x y:Ty.tySem (Word 8)):@literal_y_from_x Alg.CoreFunSem x=inr y ->
 0<=@toZ (WordToZ 8) y<feP.
Proof.
 rewrite literal_y_from_x_step,literal_root_result_step.
 destruct (@canonical_fe_is_zero Alg.CoreFunSem _) as [u|u];[discriminate|].
 intro Equal.
 pose proof (f_equal (fun v:(Datatypes.unit+Ty.tySem (Word 8))%type=>
   match v with inl _=>y|inr value=>value end) Equal) as Payload.
 change (literal_root_candidate
  (@literal_fe_add Alg.CoreFunSem (curve_seven_word,@literal_fe_cube Alg.CoreFunSem x))=y) in Payload.
 rewrite <-Payload;apply decompress_root_candidate_range.
Qed.
Lemma literal_fe_negate_involutive_normalized (y:Ty.tySem (Word 8)):0<=@toZ (WordToZ 8) y<feP ->
 @literal_fe_negate Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem y)=y.
Proof.
 intro Range;apply (toZ_injective (WordToZ 8)).
 rewrite !literal_curve_negate_numeric.
 rewrite Zminus_mod_idemp_r.
 replace (feP-(feP-@toZ (WordToZ 8) y)) with (@toZ (WordToZ 8) y) by ring.
 apply Z.mod_small;exact Range.
Qed.
Lemma literal_decompress_opposite_parity (x:Ty.tySem (Word 8)):
 @literal_decompress Alg.CoreFunSem (inr tt,x)=
 match @literal_decompress Alg.CoreFunSem (inl tt,x) with
 | inl _=>inl tt
 | inr p=>inr (@literal_ge_negate Alg.CoreFunSem p)
 end.
Proof.
 rewrite !literal_decompress_step.
 destruct (@literal_y_from_x Alg.CoreFunSem x) as [u|y] eqn:Root;[destruct u;reflexivity|].
 pose proof (decompress_y_from_x_range x y Root) as Range.
 change ((@inr Datatypes.unit _ (@canonical_fe_normalize Alg.CoreFunSem x,
   if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) Datatypes.true
    then @literal_fe_negate Alg.CoreFunSem y else y))=
 inr (@literal_ge_negate Alg.CoreFunSem
  (@canonical_fe_normalize Alg.CoreFunSem x,
   if xorb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)) Datatypes.false
    then @literal_fe_negate Alg.CoreFunSem y else y))).
 destruct (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y));
 cbn [xorb];rewrite literal_ge_negate_step,canonical_fe_normalize_idempotent.
 - rewrite literal_fe_negate_involutive_normalized by exact Range;reflexivity.
 - reflexivity.
Qed.

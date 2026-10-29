(** Route the canonical B-then-A decode through the C A-then-B guard order. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_point_verify_literal C.jet_secp_linear_verify_literal
 C.jet_secp_decompress_literal C.jet_secp_curve_literal C.jet_secp_add_literal
 C.jet_secp_literal_add_program C.jet_secp_strauss_complete_program C.jet_secp_gej_negate_literal C.jet_secp_literal_gej_predicate.
Set Default Timeout 10.
Local Opaque literal_point_check literal_linear_check literal_decompress literal_ge_is_on_curve
 literal_off_curve_linear_combination_1 literal_ge_negate literal_gej_ge_add literal_gej_is_infinity literal_fe_one256.

Lemma point_verify_check_route (na ng:Ty.tySem (Word 8))
 (a b:Ty.tySem literal_compressed_point) (ap bp:Ty.tySem (Ty.Prod (Word 8) (Word 8)))
 (goodA goodB:bool) :
 @literal_decompress Alg.CoreFunSem a=(if goodA then inr ap else inl tt) ->
 @literal_decompress Alg.CoreFunSem b=(if goodB then inr bp else inl tt) ->
 (goodA=Datatypes.true -> Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem ap)=Datatypes.true) ->
 (goodB=Datatypes.true -> Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem bp)=Datatypes.true) ->
 Bit.toBool (@literal_point_check Alg.CoreFunSem (((na,a),ng),b))=
 andb goodA (andb goodB
  (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem
      (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
        ((na,(ap,@literal_fe_one256 Alg.CoreFunSem tt)),ng),@literal_ge_negate Alg.CoreFunSem bp))))).
Proof.
 intros A B CurveA CurveB;rewrite literal_point_check_value,A,B.
 destruct goodA,goodB;cbn.
 - rewrite literal_linear_check_value,CurveA,CurveB by reflexivity;reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.

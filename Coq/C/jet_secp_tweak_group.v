(** Discharge curve validity of the native tweak result using checked Strauss. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_curve_group_power
 C.jet_secp_lookup5_group C.jet_secp_signed_group_action C.jet_secp_generate_group C.jet_secp_field_word_group
 C.jet_secp_jacobian_word_group C.jet_secp_jacobian_mixed_word_group C.jet_secp_table_pass2_group
 C.jet_secp_affine_word_valid C.jet_secp_strauss_complete_program C.jet_secp_strauss_body_group C.jet_secp_norm_group C.jet_secp_even_x_test
 C.jet_secp_curve_literal C.jet_secp_literal_gej_predicate C.jet_secp_literal_add_program C.jet_secp_gej_norm_literal
 C.jet_secp_canonical_scalar C.jet_secp_eckey_tweak_prepare C.jet_secp_eckey_tweak_function
 C.jet_secp_tweak_bytes_function C.jet_secp_xonly_tweak_function C.jet_secp_ge_storage_body
 C.jet_secp_multiply_normalize_bridge C.jet_secp_fe_inv_prefix C.jet_secp_rescale_literal C.jet_secp_multiply_finish_product
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_secp_pubkey_load_coordinates.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Local Opaque literal_strauss_body literal_gej_norm literal_gej_is_infinity secp_field_word
 secp_group_signed_power SMain.add canonical_scalar_normalize rescale_field_output.
Theorem eckey_tweak_point_group (ng ax ay:Ty.tySem (Word 8)) (p:secp_group_point):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 secp_affine_word_rep (GZnZ.one feP) (ax,ay) p ->
 secp_jacobian_word_rep (GZnZ.one feP) (eckey_tweak_point ng ax ay)
 (p⊕secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))).
Proof.
 intros Curve Input;unfold eckey_tweak_point.
 pose proof (secp_literal_strauss_body_affine_group eckey_scalar_one ng ax ay p Curve Input) as Output.
 rewrite eckey_scalar_one_value,secp_generator_signed_one in Output;exact Output.
Qed.
Theorem eckey_tweak_norm_group (ng ax ay:Ty.tySem (Word 8)) (p:secp_group_point):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 secp_affine_word_rep (GZnZ.one feP) (ax,ay) p ->eckey_tweak_infinite ng ax ay=Datatypes.false ->
 secp_affine_word_rep (GZnZ.one feP)
 (@literal_gej_norm Alg.CoreFunSem (eckey_tweak_point ng ax ay))
 (p⊕secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))).
Proof.
 intros Curve Input Finite.
 pose proof (eckey_tweak_point_group ng ax ay p Curve Input) as Output.
 unfold eckey_tweak_infinite in Finite.
 destruct (eckey_tweak_point ng ax ay) as [[x y] z].
 apply secp_literal_gej_norm_group;[|exact Output].
 intro Zero;apply (proj2 (secp_field_word_flag_true z)) in Zero.
 rewrite literal_gej_is_infinity_value in Finite;congruence.
Qed.
Theorem eckey_tweak_value_curve (ng ax ay x y:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 eckey_tweak_value ng ax ay=Some (x,y) ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true.
Proof.
 intros Curve Value;destruct (secp_affine_literal_represented ax ay Curve) as [p Input].
 unfold eckey_tweak_value in Value;destruct (eckey_tweak_infinite ng ax ay) eqn:Infinite;[discriminate|].
 assert (Pair:@literal_gej_norm Alg.CoreFunSem (eckey_tweak_point ng ax ay)=(x,y)).
 { exact (f_equal (fun v:option (Ty.tySem (Ty.Prod (Word 8) (Word 8)))=>
   match v with Some point=>point|None=>(x,y) end) Value). }
 pose proof (eckey_tweak_norm_group ng ax ay p Curve Input Infinite) as Normalized.
 rewrite Pair in Normalized;exact (secp_affine_word_rep_curve x y _ Normalized).
Qed.
Theorem tweak_bytes_value_curve (ng ax ay x y:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 tweak_bytes_value ng ax ay=Some (x,y) ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true.
Proof.
 intros Curve Value;unfold tweak_bytes_value in Value;destruct (tweak_bytes_overflow ng);[discriminate|].
 exact (eckey_tweak_value_curve ng ax ay x y Curve Value).
Qed.
Theorem xonly_tweak_saved_coordinates value m b:
 xonly_tweak_saved_result (Some value) m b ->exists w,
 affine_storage_readable m b 0 w /\field_storage_value w=@toZ (WordToZ 8) (fst value) /\
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) (snd value).
Proof.
 intros (x & y & Stored & BX & BY & Pair);exists (ge_storage_words x y);split;[exact Stored|].
 rewrite <-Pair;cbn [fst snd];rewrite (proj1 (ge_storage_words_values x y)),(proj2 (ge_storage_words_values x y)).
 rewrite !rescale_field_output_value,!field_prime_matches_normalizer;split;reflexivity.
Qed.
Theorem xonly_tweak_saved_loadable (ng ax ay x y:Ty.tySem (Word 8)) m b:
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 tweak_bytes_value ng ax ay=Some (x,y) ->xonly_tweak_saved_result (Some (x,y)) m b ->exists w,
 affine_storage_readable m b 0 w /\field_storage_value w=@toZ (WordToZ 8) x /\
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) y /\
 C.jet_secp_pubkey_load_body.pubkey_storage_accept w=Datatypes.true.
Proof.
 intros Curve Value Saved;destruct (xonly_tweak_saved_coordinates (x,y) m b Saved) as (w & Stored & X & Y).
 exists w;split;[exact Stored|];split;[exact X|];split;[exact Y|].
 apply pubkey_storage_accept_curve with (x:=x) (y:=y);[exact X|].
 exact (tweak_bytes_value_curve ng ax ay x y Curve Value).
Qed.

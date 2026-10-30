(** Recover the canonical X and curve validity after the real even-Y conversion. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_field_word_group C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group
 C.jet_secp_affine_word_valid C.jet_secp_even_x_test C.jet_secp_lookup5_group C.jet_secp_gej_negate_literal
 C.jet_secp_curve_literal C.jet_secp_canonical_normalize C.jet_secp_affine_storage C.jet_secp_storage_numeric
 C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_canonical_scalar C.jet_secp_field_mul_small C.jet_secp_field_odd_words
 C.jet_secp_swu_word_parity C.jet_secp_extrakeys_even_y C.jet_secp_xonly_from_pubkey C.jet_secp_tweak_group
 C.jet_secp_xonly_tweak_function C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque rescale_field_output canonical_fe_normalize literal_ge_negate literal_ge_is_on_curve secp_field_word.
Lemma affine_storage_decoded_word w (k:bool) a:
 field_storage_value (fun i=>w ((if k then 4 else 0)+i)%nat)=@toZ (WordToZ 8) a ->
 rescale_field_output (affine_storage_coord w k)=@canonical_fe_normalize Alg.CoreFunSem a.
Proof.
 intro Value;apply (toZ_injective (WordToZ 8)).
 rewrite rescale_field_output_value,field_prime_matches_normalizer,canonical_fe_normalize_numeric,
 canonical_field_order_matches_limb_model.
 unfold affine_storage_coord;rewrite storage_unpack_preserves_value,Value;reflexivity.
Qed.
Lemma secp_affine_normalized_curve (ax ay:Ty.tySem (Word 8)):
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem
  (@canonical_fe_normalize Alg.CoreFunSem ax,@canonical_fe_normalize Alg.CoreFunSem ay))=true.
Proof.
 intro Curve;destruct (secp_affine_literal_represented ax ay Curve) as [p Input].
 apply secp_affine_word_rep_curve with (p:=p).
 unfold secp_affine_word_rep,secp_jacobian_word_rep,secp_jacobian_word_fields;cbn [fst snd].
 rewrite !secp_field_word_normalize;exact Input.
Qed.
Theorem xonly_from_value_curve w (ax ay:Ty.tySem (Word 8)):
 field_storage_value w=@toZ (WordToZ 8) ax ->field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (xonly_from_value w))=true.
Proof.
 intros X Y Curve.
 assert (Start:Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem
  (rescale_field_output (affine_storage_coord w false),rescale_field_output (affine_storage_coord w true)))=true).
 { rewrite (affine_storage_decoded_word w false ax X),(affine_storage_decoded_word w true ay Y).
   apply secp_affine_normalized_curve;exact Curve. }
 pose proof (swu_words_parity_matches_literal (affine_storage_coord w true)
  (affine_storage_coord w false) (affine_storage_coord w true) (affine_storage_small_bounds w true)) as Value.
 change (xonly_from_value w=if field_words_odd (affine_storage_coord w true) then
  @literal_ge_negate Alg.CoreFunSem
   (rescale_field_output (affine_storage_coord w false),rescale_field_output (affine_storage_coord w true))
  else (rescale_field_output (affine_storage_coord w false),rescale_field_output (affine_storage_coord w true))) in Value.
 rewrite Value;destruct (field_words_odd (affine_storage_coord w true));[|exact Start].
 destruct (secp_affine_literal_represented _ _ Start) as [p Represented].
 pose proof (secp_affine_negate_group (GZnZ.one feP) _ p Represented) as Negative.
 destruct (@literal_ge_negate Alg.CoreFunSem
   (rescale_field_output (affine_storage_coord w false),rescale_field_output (affine_storage_coord w true))) as [x y].
 exact (secp_affine_word_rep_curve x y _ Negative).
Qed.
Theorem xonly_from_saved_ready w (ax ay:Ty.tySem (Word 8)) m b:
 field_storage_value w=@toZ (WordToZ 8) ax ->field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true ->
 xonly_tweak_saved_result (Some (xonly_from_value w)) m b ->exists storage outy,
 affine_storage_readable m b 0 storage /\field_storage_value storage=@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem ax) /\
 field_storage_value (fun i=>storage (4+i)%nat)=@toZ (WordToZ 8) outy /\
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem ax,outy))=true.
Proof.
 intros X Y Curve Saved.
 destruct (xonly_tweak_saved_coordinates (xonly_from_value w) m b Saved) as (storage & Stored & SX & SY).
 exists storage,(snd (xonly_from_value w));split;[exact Stored|];split.
 - change (field_storage_value storage=@toZ (WordToZ 8) (rescale_field_output (affine_storage_coord w false))) in SX.
   rewrite (affine_storage_decoded_word w false ax X) in SX;exact SX.
 - split;[exact SY|].
   rewrite <-(affine_storage_decoded_word w false ax X).
   exact (xonly_from_value_curve w ax ay X Y Curve).
Qed.

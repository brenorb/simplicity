(** Reusable literal tagged-tweak program and option semantics for any initial SHA state. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit Simplicity.Util.Option.
Require Simplicity.SHA256.
Require Import C.jet_assertion_spec C.jet_order_spec C.jet_secp_canonical_normalize C.jet_secp_canonical_scalar
 C.jet_secp_scalar_table_literal C.jet_secp_add_literal C.jet_secp_gej_norm_branch C.jet_secp_decompress_literal C.jet_secp_generate_program C.jet_secp_literal_add_program C.jet_secp_gej_norm_literal
 C.jet_secp_taptweak_tag C.jet_secp_taptweak_hash.
Require Import C.jet_secp_taptweak_finish C.jet_secp_taptweak_parsed_native C.jet_secp_tweak_add_equivalence
 C.jet_secp_literal_gej_predicate C.jet_secp_even_x_test C.jet_secp_even_y_unique C.jet_secp_affine_word_valid C.jet_secp_tweak_bytes_function.
Set Default Timeout 10.
Require Import C.jet_secp_taptweak_literal.
Module TC:=Alg.Core.Combinators.
Section TaggedTweak.
Variable iv:Ty.tySem(Word 8).
Definition tagged_taptweak_hash_word(pk h:Ty.tySem(Word 8)):=
 @Simplicity.SHA256.hashBlock Alg.CoreFunSem
 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem(iv,(pk,h)),taptweak_pad_word).
Definition literal_taptweak_hash_at {term:Alg.Assertion.Algebra}:term (Word 9) (Word 8):=
 let core:=Alg.Assertion.toCore term in
 TC.comp
  (TC.comp (TC.pair
    (TC.comp (taptweak_assert (TC.comp (TC.pair (TC.take TC.iden) (@Alg.scribe (Word 9) (Word 8) canonical_field_word core))
       (@lt_word_spec core 8))) (@Alg.scribe Ty.Unit (Word 8) iv core)) TC.iden)
    (@Simplicity.SHA256.hashBlock core))
  (TC.comp (TC.pair TC.iden (@Alg.scribe (Word 8) (Word 9) taptweak_pad_word core)) (@Simplicity.SHA256.hashBlock core)).
Definition literal_taptweak_generate_at {term:Alg.Assertion.Algebra}:term (Word 9) literal_table_gej:=
 let core:=Alg.Assertion.toCore term in
 TC.comp (@literal_taptweak_hash_at term)
  (TC.comp (TC.pair
    (taptweak_assert (TC.comp (TC.pair TC.iden (@Alg.scribe (Word 8) (Word 8) canonical_group_word core)) (@lt_word_spec core 8))) TC.iden)
   (TC.drop (@literal_generate core))).
Definition literal_taptweak_at {term:Alg.Assertion.Algebra}:term (Word 9) (Word 8):=
 let core:=Alg.Assertion.toCore term in
 TC.comp
 (taptweak_assert (TC.comp
   (TC.comp (TC.pair (@literal_taptweak_generate_at term) (@literal_taptweak_parse term)) (@literal_gej_ge_add core))
   (@literal_gej_normalize core))) (TC.take TC.iden).
Local Opaque Simplicity.SHA256.hashBlock lt_word_spec Alg.scribe canonical_field_word canonical_group_word taptweak_pad_word.
Lemma literal_taptweak_hash_at_parametric:Alg.Assertion.Parametric (@literal_taptweak_hash_at).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak_hash_at,taptweak_assert.
 repeat first [apply (Simplicity.SHA256.hashBlock_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (lt_word_spec_parametric 8 _ _ (Alg.Core.Parametric.Pack HC))|
 apply (Alg.scribe_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.drop_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))].
Qed.

Local Opaque literal_taptweak_hash_at literal_generate literal_decompress literal_gej_ge_add literal_gej_normalize.
Lemma literal_taptweak_generate_at_parametric:Alg.Assertion.Parametric (@literal_taptweak_generate_at).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak_generate_at,taptweak_assert.
 repeat first [apply (literal_taptweak_hash_at_parametric _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))|
 apply (literal_generate_parametric _ _ (Alg.Core.Parametric.Pack HC))|
 apply (lt_word_spec_parametric 8 _ _ (Alg.Core.Parametric.Pack HC))|
 apply (Alg.scribe_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.drop_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))].
Qed.
Local Opaque literal_taptweak_generate_at literal_taptweak_parse.
Lemma literal_taptweak_parametric_at:Alg.Assertion.Parametric (@literal_taptweak_at).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak_at,taptweak_assert.
 repeat first [apply (literal_taptweak_generate_at_parametric _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))|
 apply (literal_taptweak_parse_parametric _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))|
 apply (literal_gej_ge_add_parametric _ _ (Alg.Core.Parametric.Pack HC))|
 apply (literal_gej_normalize_parametric _ _ (Alg.Core.Parametric.Pack HC))|
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))].
Qed.
Local Transparent literal_taptweak_hash_at.
Lemma literal_taptweak_hash_at_option (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_hash_at (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 if Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order then Some (tagged_taptweak_hash_word pk h) else None.
Proof.
 unfold literal_taptweak_hash_at.
 repeat first [rewrite taptweak_option_comp|rewrite taptweak_option_pair|
 rewrite taptweak_assert_option|rewrite taptweak_option_take|rewrite taptweak_option_iden|
 rewrite taptweak_scribe_option|rewrite taptweak_lt_option|rewrite taptweak_hashblock_option|
 progress cbn [option_bind option_join option_map]].
 pose proof (lt_word_spec_numeric 8 pk canonical_field_word) as Compare.
 rewrite canonical_field_word_value in Compare.
 rewrite <-Compare.
 destruct (@lt_word_spec Alg.CoreFunSem 8 (pk,canonical_field_word)) as [u|u] eqn:Flag;destruct u.
 - lazymatch goal with |- context[@lt_word_spec ?alg ?n ?arg] =>
   assert (Actual:@lt_word_spec alg n arg=Bit.zero) by exact Flag;rewrite Actual end.
   reflexivity.
 - lazymatch goal with |- context[@lt_word_spec ?alg ?n ?arg] =>
   assert (Actual:@lt_word_spec alg n arg=Bit.one) by exact Flag;rewrite Actual end.
   repeat first [rewrite taptweak_option_comp|rewrite taptweak_option_pair|
   rewrite taptweak_option_iden|rewrite taptweak_scribe_option|rewrite taptweak_hashblock_option|
   progress cbn [option_bind option_join option_map Bit.toBool]].
   reflexivity.
Qed.
Local Opaque literal_taptweak_hash_at.
Local Ltac taptweak_option_reduce:=repeat first [rewrite taptweak_option_comp|rewrite taptweak_option_pair|
 rewrite taptweak_assert_option|rewrite taptweak_option_take|rewrite taptweak_option_drop|
 rewrite taptweak_option_iden|rewrite taptweak_option_unit|rewrite taptweak_scribe_option|
 rewrite taptweak_lt_option|rewrite taptweak_hashblock_option|
 progress cbn [option_bind option_join option_map]].
Local Transparent literal_taptweak_generate_at.
Lemma literal_taptweak_generate_at_option (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_generate_at (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 if Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order then
  if Z.ltb (@toZ (WordToZ 8) (tagged_taptweak_hash_word pk h)) canonical_group_order
  then Some (@literal_generate Alg.CoreFunSem (tagged_taptweak_hash_word pk h)) else None
 else None.
Proof.
 unfold literal_taptweak_generate_at;rewrite taptweak_option_comp,literal_taptweak_hash_at_option.
 destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
 taptweak_option_reduce.
 pose proof (lt_word_spec_numeric 8 (tagged_taptweak_hash_word pk h) canonical_group_word) as Compare.
 rewrite canonical_group_word_value in Compare;rewrite <-Compare.
 destruct (@lt_word_spec Alg.CoreFunSem 8 (tagged_taptweak_hash_word pk h,canonical_group_word)) as [u|u] eqn:Flag;destruct u.
 - lazymatch goal with |- context[@lt_word_spec ?alg ?n ?arg] =>
   assert (Actual:@lt_word_spec alg n arg=Bit.zero) by exact Flag;rewrite Actual end;reflexivity.
 - lazymatch goal with |- context[@lt_word_spec ?alg ?n ?arg] =>
   assert (Actual:@lt_word_spec alg n arg=Bit.one) by exact Flag;rewrite Actual end.
   taptweak_option_reduce;rewrite taptweak_generate_option;reflexivity.
Qed.
Local Opaque literal_taptweak_generate_at literal_taptweak_parse.
Lemma literal_taptweak_option_at (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_at (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 if Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order then
  if Z.ltb (@toZ (WordToZ 8) (tagged_taptweak_hash_word pk h)) canonical_group_order then
   match @literal_decompress Alg.CoreFunSem (inl tt,pk) with inl _=>None|inr xy=>
    match @literal_gej_normalize Alg.CoreFunSem
     (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem (tagged_taptweak_hash_word pk h),xy))
    with inl _=>None|inr output=>Some (fst output) end end
  else None else None.
Proof.
 unfold literal_taptweak_at;taptweak_option_reduce.
 rewrite literal_taptweak_generate_at_option,literal_taptweak_parse_option.
 destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
 destruct (Z.ltb (@toZ (WordToZ 8) (tagged_taptweak_hash_word pk h)) canonical_group_order);[|reflexivity].
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,pk)) as [u|xy];[reflexivity|].
 taptweak_option_reduce;rewrite taptweak_add_option;taptweak_option_reduce.
 rewrite taptweak_normalize_option;taptweak_option_reduce.
 destruct (@literal_gej_normalize Alg.CoreFunSem
  (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem (tagged_taptweak_hash_word pk h),xy))) as [u | [x y]] eqn:Norm.
 - repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
   let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inl u) by exact Norm;rewrite Actual end;reflexivity.
 - repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
   let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inr (x,y)) by exact Norm;rewrite Actual end.
   taptweak_option_reduce;reflexivity.
Qed.

Local Opaque canonical_fe_normalize.
Theorem literal_taptweak_matches_output_at (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_at (Alg.AssertionSem option_Monad_Zero) (pk,h)=taptweak_output (tagged_taptweak_hash_word pk h) pk.
Proof.
 rewrite literal_taptweak_option_at.
 unfold taptweak_output,taptweak_value.
 rewrite <-canonical_field_order_matches_limb_model.
 destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,pk)) as [u | [ax ay]] eqn:Decode;[destruct u;destruct (Z.ltb (@toZ (WordToZ 8) (tagged_taptweak_hash_word pk h)) canonical_group_order);reflexivity|].
 rewrite (tweak_bytes_value_matches_add _ ax ay (secp_decompress_curve pk (inl tt) (ax,ay) Decode)).
 unfold tweak_bytes_overflow.
 destruct (Z.ltb (@toZ (WordToZ 8) (tagged_taptweak_hash_word pk h)) canonical_group_order) eqn:Bound.
 - apply Z.ltb_lt in Bound;rewrite (proj2 (Z.leb_gt _ _) Bound).
   destruct (@literal_gej_normalize Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem (tagged_taptweak_hash_word pk h),(ax,ay))))
    as [u|xy] eqn:Normalized.
   + repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
     let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inl u) by exact Normalized;rewrite Actual end;reflexivity.
   + repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
     let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inr xy) by exact Normalized;rewrite Actual end.
     cbn [Coqlib.option_map];f_equal;symmetry;exact (taptweak_normalized_x _ _ Normalized).
 - apply Z.ltb_ge in Bound;rewrite (proj2 (Z.leb_le _ _) Bound);reflexivity.
Qed.
End TaggedTweak.

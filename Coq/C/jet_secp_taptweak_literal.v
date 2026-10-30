(** Literal frozen Programs.Bitcoin.buildTaptweak, including its four assertions. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit Simplicity.Util.Option.
Require Simplicity.SHA256.
Require Import C.jet_assertion_spec C.jet_order_spec C.jet_secp_canonical_normalize C.jet_secp_canonical_scalar
 C.jet_secp_scalar_table_literal C.jet_secp_add_literal C.jet_secp_gej_norm_branch C.jet_secp_decompress_literal C.jet_secp_generate_program C.jet_secp_literal_add_program C.jet_secp_gej_norm_literal
 C.jet_secp_taptweak_tag C.jet_secp_taptweak_hash.
Require Import C.jet_secp_taptweak_finish C.jet_secp_taptweak_parsed_native C.jet_secp_tweak_add_equivalence
 C.jet_secp_literal_gej_predicate C.jet_secp_even_x_test C.jet_secp_even_y_unique C.jet_secp_affine_word_valid C.jet_secp_tweak_bytes_function.
Set Default Timeout 10.
Module TC:=Alg.Core.Combinators.
Definition taptweak_assert {A B:Ty.Ty} {term:Alg.Assertion.Algebra}
 (f:term A (Ty.Sum Ty.Unit B)):term A B:=
 TC.comp (TC.pair f TC.unit) (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (TC.take TC.iden)).
Definition literal_taptweak_hash {term:Alg.Assertion.Algebra}:term (Word 9) (Word 8):=
 let core:=Alg.Assertion.toCore term in
 TC.comp
  (TC.comp (TC.pair
    (TC.comp (taptweak_assert (TC.comp (TC.pair (TC.take TC.iden) (@Alg.scribe (Word 9) (Word 8) canonical_field_word core))
       (@lt_word_spec core 8))) (@Alg.scribe Ty.Unit (Word 8) taptweak_iv_word core)) TC.iden)
    (@Simplicity.SHA256.hashBlock core))
  (TC.comp (TC.pair TC.iden (@Alg.scribe (Word 8) (Word 9) taptweak_pad_word core)) (@Simplicity.SHA256.hashBlock core)).
Definition literal_taptweak_generate {term:Alg.Assertion.Algebra}:term (Word 9) literal_table_gej:=
 let core:=Alg.Assertion.toCore term in
 TC.comp (@literal_taptweak_hash term)
  (TC.comp (TC.pair
    (taptweak_assert (TC.comp (TC.pair TC.iden (@Alg.scribe (Word 8) (Word 8) canonical_group_word core)) (@lt_word_spec core 8))) TC.iden)
   (TC.drop (@literal_generate core))).
Definition literal_taptweak_parse {term:Alg.Assertion.Algebra}:term (Word 9) (Ty.Prod (Word 8) (Word 8)):=
 let core:=Alg.Assertion.toCore term in
 taptweak_assert (TC.comp (TC.pair (TC.comp TC.unit (@Bit.false Ty.Unit core)) (TC.take TC.iden)) (@literal_decompress core)).
Definition literal_taptweak {term:Alg.Assertion.Algebra}:term (Word 9) (Word 8):=
 let core:=Alg.Assertion.toCore term in
 TC.comp
 (taptweak_assert (TC.comp
   (TC.comp (TC.pair (@literal_taptweak_generate term) (@literal_taptweak_parse term)) (@literal_gej_ge_add core))
   (@literal_gej_normalize core))) (TC.take TC.iden).
Lemma taptweak_assert_parametric {A B} (f:forall term:Alg.Assertion.Algebra,term A (Ty.Sum Ty.Unit B)):
 Alg.Assertion.Parametric f ->Alg.Assertion.Parametric (fun term=>@taptweak_assert A B term (f term)).
Proof.
 intros F a b [R [HC HA]];unfold taptweak_assert.
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC)).
   + apply (F _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   + apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC)).
 - apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
   apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC));apply Alg.iden_Parametric.
Qed.
Local Opaque Simplicity.SHA256.hashBlock lt_word_spec Alg.scribe canonical_field_word canonical_group_word taptweak_iv_word taptweak_pad_word.
Lemma literal_taptweak_hash_parametric:Alg.Assertion.Parametric (@literal_taptweak_hash).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak_hash,taptweak_assert.
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

Local Opaque literal_taptweak_hash literal_generate literal_decompress literal_gej_ge_add literal_gej_normalize.
Lemma literal_taptweak_generate_parametric:Alg.Assertion.Parametric (@literal_taptweak_generate).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak_generate,taptweak_assert.
 repeat first [apply (literal_taptweak_hash_parametric _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))|
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
Lemma literal_taptweak_parse_parametric:Alg.Assertion.Parametric (@literal_taptweak_parse).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak_parse,taptweak_assert.
 repeat first [apply (literal_decompress_parametric _ _ (Alg.Core.Parametric.Pack HC))|
 apply (Bit.false_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.iden_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.unit_Parametric (Alg.Core.Parametric.Pack HC))|
 apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))].
Qed.
Local Opaque literal_taptweak_generate literal_taptweak_parse.
Lemma literal_taptweak_parametric:Alg.Assertion.Parametric (@literal_taptweak).
Proof.
 intros a b [R [HC HA]];unfold literal_taptweak,taptweak_assert.
 repeat first [apply (literal_taptweak_generate_parametric _ _ (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)))|
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
Lemma taptweak_assert_option {A B} (f:Alg.AssertionSem option_Monad_Zero A (Ty.Sum Ty.Unit B)) (x:Ty.tySem A):
 @taptweak_assert A B (Alg.AssertionSem option_Monad_Zero) f x=
 match f x with None=>None|Some (inl _)=>None|Some (inr value)=>Some value end.
Proof.
 unfold taptweak_assert,TC.comp,TC.pair,TC.unit,TC.take,TC.iden,Alg.Assertion.Combinators.assertr.
 cbn [Alg.Core.comp Alg.Core.pair Alg.Core.unit Alg.Core.take Alg.Core.iden Alg.Core.class_of
 Alg.Assertion.toCore Alg.Assertion.base Alg.Assertion.class_of Alg.Assertion.packager
 Alg.Assertion.assertr Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin
 Monad.CIMonad.Theory.kleisliComp].
 unfold Monad.CIMonad.Theory.kleisliComp.
 cbv [Monad.CIMonad.kleisliComp Monad.CIMonad.class_of Monad.MonadZero.to_Monad
 Monad.MonadZero.class_of Monad.MonadZero.base Monad.MonadZero.packager
 option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 cbn [Monad.CIMonad.Theory.phi Monad.CIMonad.Theory.eta Monad.CIMonad.bind option_bind].
 destruct (f x) as [z|].
 - destruct z as [u|v].
   + destruct u;reflexivity.
   + reflexivity.
 - reflexivity.
Qed.
Lemma taptweak_option_comp {A B C:Ty.Ty}
 (f:Alg.AssertionSem option_Monad_Zero A B) (g:Alg.AssertionSem option_Monad_Zero B C) x:
 TC.comp f g x=option_bind g (f x).
Proof. reflexivity. Qed.
Lemma taptweak_option_pair {A B C:Ty.Ty}
 (f:Alg.AssertionSem option_Monad_Zero A B) (g:Alg.AssertionSem option_Monad_Zero A C) x:
 TC.pair f g x=option_bind (fun a=>option_map (fun b=>(a,b)) (g x)) (f x).
Proof.
 unfold TC.pair.
 cbn [Alg.Core.pair Alg.Core.class_of Alg.Assertion.toCore Alg.Assertion.base Alg.Assertion.class_of
 Alg.Assertion.packager Alg.AssertionSem Alg.AssertionSem_mixin Alg.CoreSem Alg.CoreSem_mixin].
 cbv [Monad.CIMonad.class_of Monad.MonadZero.to_Monad Monad.MonadZero.class_of Monad.MonadZero.base
 Monad.MonadZero.packager option_Monad_Zero option_MonadZero_mixin option_CIMonad option_CIMonad_class].
 cbn [Monad.CIMonad.Theory.phi Monad.CIMonad.Theory.eta Monad.CIMonad.bind option_bind].
 destruct (f x), (g x);reflexivity.
Qed.
Lemma taptweak_option_take {A B C:Ty.Ty} (f:Alg.AssertionSem option_Monad_Zero A C) (a:Ty.tySem A) (b:Ty.tySem B):
 TC.take f (a,b)=f a.
Proof. reflexivity. Qed.
Lemma taptweak_option_drop {A B C:Ty.Ty} (f:Alg.AssertionSem option_Monad_Zero B C) (a:Ty.tySem A) (b:Ty.tySem B):
 TC.drop f (a,b)=f b.
Proof. reflexivity. Qed.
Lemma taptweak_option_iden {A:Ty.Ty} (a:Ty.tySem A):
 @TC.iden A (Alg.AssertionSem option_Monad_Zero) a=Some a.
Proof. reflexivity. Qed.
Lemma taptweak_option_unit {A:Ty.Ty} (a:Ty.tySem A):
 @TC.unit A (Alg.AssertionSem option_Monad_Zero) a=Some tt.
Proof. reflexivity. Qed.
Lemma taptweak_core_option {A B:Ty.Ty} (f:forall term:Alg.Core.Algebra,term A B) (P:Alg.Core.Parametric f) x:
 f (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) x=Some (f Alg.CoreFunSem x).
Proof. exact (Alg.CoreSem_initial (M:=option_CIMonad) P x). Qed.
Lemma taptweak_scribe_option {A B:Ty.Ty} (b:Ty.tySem B) (x:Ty.tySem A):
 @Alg.scribe A B b (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) x=Some b.
Proof. rewrite (taptweak_core_option (fun alg=>@Alg.scribe A B b alg) (fun a b R=>Alg.scribe_Parametric R _) x).
 rewrite Alg.scribe_correct;reflexivity. Qed.
Lemma taptweak_lt_option x y:
 @lt_word_spec (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) 8 (x,y)=
 Some (@lt_word_spec Alg.CoreFunSem 8 (x,y)).
Proof. exact (taptweak_core_option (fun alg=>@lt_word_spec alg 8) (lt_word_spec_parametric 8) (x,y)). Qed.
Lemma taptweak_hashblock_option x:
 @Simplicity.SHA256.hashBlock (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) x=
 Some (@Simplicity.SHA256.hashBlock Alg.CoreFunSem x).
Proof. exact (taptweak_core_option (@Simplicity.SHA256.hashBlock) (@Simplicity.SHA256.hashBlock_Parametric) x). Qed.
Local Transparent literal_taptweak_hash.
Lemma literal_taptweak_hash_option (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_hash (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 if Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order then Some (taptweak_hash_word pk h) else None.
Proof.
 unfold literal_taptweak_hash.
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
Local Opaque literal_taptweak_hash.
Local Ltac taptweak_option_reduce:=repeat first [rewrite taptweak_option_comp|rewrite taptweak_option_pair|
 rewrite taptweak_assert_option|rewrite taptweak_option_take|rewrite taptweak_option_drop|
 rewrite taptweak_option_iden|rewrite taptweak_option_unit|rewrite taptweak_scribe_option|
 rewrite taptweak_lt_option|rewrite taptweak_hashblock_option|
 progress cbn [option_bind option_join option_map]].
Lemma taptweak_generate_option ng:
 @literal_generate (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) ng=
 Some (@literal_generate Alg.CoreFunSem ng).
Proof. exact (taptweak_core_option (@literal_generate) literal_generate_parametric ng). Qed.
Local Transparent literal_taptweak_generate.
Lemma literal_taptweak_generate_option (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_generate (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 if Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order then
  if Z.ltb (@toZ (WordToZ 8) (taptweak_hash_word pk h)) canonical_group_order
  then Some (@literal_generate Alg.CoreFunSem (taptweak_hash_word pk h)) else None
 else None.
Proof.
 unfold literal_taptweak_generate;rewrite taptweak_option_comp,literal_taptweak_hash_option.
 destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
 taptweak_option_reduce.
 pose proof (lt_word_spec_numeric 8 (taptweak_hash_word pk h) canonical_group_word) as Compare.
 rewrite canonical_group_word_value in Compare;rewrite <-Compare.
 destruct (@lt_word_spec Alg.CoreFunSem 8 (taptweak_hash_word pk h,canonical_group_word)) as [u|u] eqn:Flag;destruct u.
 - lazymatch goal with |- context[@lt_word_spec ?alg ?n ?arg] =>
   assert (Actual:@lt_word_spec alg n arg=Bit.zero) by exact Flag;rewrite Actual end;reflexivity.
 - lazymatch goal with |- context[@lt_word_spec ?alg ?n ?arg] =>
   assert (Actual:@lt_word_spec alg n arg=Bit.one) by exact Flag;rewrite Actual end.
   taptweak_option_reduce;rewrite taptweak_generate_option;reflexivity.
Qed.
Lemma taptweak_decompress_option point:
 @literal_decompress (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) point=
 Some (@literal_decompress Alg.CoreFunSem point).
Proof. exact (taptweak_core_option (@literal_decompress) literal_decompress_parametric point). Qed.
Lemma taptweak_false_option x:
 @Bit.false Ty.Unit (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) x=Some Bit.zero.
Proof. destruct x;reflexivity. Qed.
Local Transparent literal_taptweak_parse.
Lemma literal_taptweak_parse_option (pk h:Ty.tySem (Word 8)):
 @literal_taptweak_parse (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 match @literal_decompress Alg.CoreFunSem (inl tt,pk) with inl _=>None|inr xy=>Some xy end.
Proof.
 unfold literal_taptweak_parse;taptweak_option_reduce.
 rewrite taptweak_false_option;taptweak_option_reduce.
 rewrite taptweak_decompress_option;reflexivity.
Qed.
Local Opaque literal_taptweak_generate literal_taptweak_parse.
Lemma taptweak_add_option point:
 @literal_gej_ge_add (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) point=
 Some (@literal_gej_ge_add Alg.CoreFunSem point).
Proof. exact (taptweak_core_option (@literal_gej_ge_add) literal_gej_ge_add_parametric point). Qed.
Lemma taptweak_normalize_option point:
 @literal_gej_normalize (Alg.Assertion.toCore (Alg.AssertionSem option_Monad_Zero)) point=
 Some (@literal_gej_normalize Alg.CoreFunSem point).
Proof. exact (taptweak_core_option (@literal_gej_normalize) literal_gej_normalize_parametric point). Qed.
Lemma literal_taptweak_option (pk h:Ty.tySem (Word 8)):
 @literal_taptweak (Alg.AssertionSem option_Monad_Zero) (pk,h)=
 if Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order then
  if Z.ltb (@toZ (WordToZ 8) (taptweak_hash_word pk h)) canonical_group_order then
   match @literal_decompress Alg.CoreFunSem (inl tt,pk) with inl _=>None|inr xy=>
    match @literal_gej_normalize Alg.CoreFunSem
     (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem (taptweak_hash_word pk h),xy))
    with inl _=>None|inr output=>Some (fst output) end end
  else None else None.
Proof.
 unfold literal_taptweak;taptweak_option_reduce.
 rewrite literal_taptweak_generate_option,literal_taptweak_parse_option.
 destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
 destruct (Z.ltb (@toZ (WordToZ 8) (taptweak_hash_word pk h)) canonical_group_order);[|reflexivity].
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,pk)) as [u|xy];[reflexivity|].
 taptweak_option_reduce;rewrite taptweak_add_option;taptweak_option_reduce.
 rewrite taptweak_normalize_option;taptweak_option_reduce.
 destruct (@literal_gej_normalize Alg.CoreFunSem
  (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem (taptweak_hash_word pk h),xy))) as [u | [x y]] eqn:Norm.
 - repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
   let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inl u) by exact Norm;rewrite Actual end;reflexivity.
 - repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
   let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inr (x,y)) by exact Norm;rewrite Actual end.
   taptweak_option_reduce;reflexivity.
Qed.

Local Opaque canonical_fe_normalize.
Lemma taptweak_normalized_x (point:Ty.tySem literal_table_gej) (xy:Ty.tySem (Ty.Prod (Word 8) (Word 8))):
 @literal_gej_normalize Alg.CoreFunSem point=inr xy ->@canonical_fe_normalize Alg.CoreFunSem (fst xy)=fst xy.
Proof.
 rewrite literal_gej_normalize_flag_value.
 destruct (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point));[discriminate|].
 intro Equal;inversion Equal;subst xy.
 destruct point as [[x y] z];apply secp_normalize_bounded_word;apply (proj1 (secp_gej_norm_ranges x y z)).
Qed.
Theorem literal_taptweak_matches_output (pk h:Ty.tySem (Word 8)):
 @literal_taptweak (Alg.AssertionSem option_Monad_Zero) (pk,h)=taptweak_output (taptweak_hash_word pk h) pk.
Proof.
 rewrite literal_taptweak_option.
 unfold taptweak_output,taptweak_value.
 rewrite <-canonical_field_order_matches_limb_model.
 destruct (Z.ltb (@toZ (WordToZ 8) pk) canonical_field_order);[|reflexivity].
 destruct (@literal_decompress Alg.CoreFunSem (inl tt,pk)) as [u | [ax ay]] eqn:Decode;[destruct u;destruct (Z.ltb (@toZ (WordToZ 8) (taptweak_hash_word pk h)) canonical_group_order);reflexivity|].
 rewrite (tweak_bytes_value_matches_add _ ax ay (secp_decompress_curve pk (inl tt) (ax,ay) Decode)).
 unfold tweak_bytes_overflow.
 destruct (Z.ltb (@toZ (WordToZ 8) (taptweak_hash_word pk h)) canonical_group_order) eqn:Bound.
 - apply Z.ltb_lt in Bound;rewrite (proj2 (Z.leb_gt _ _) Bound).
   destruct (@literal_gej_normalize Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem (@literal_generate Alg.CoreFunSem (taptweak_hash_word pk h),(ax,ay))))
    as [u|xy] eqn:Normalized.
   + repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
     let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inl u) by exact Normalized;rewrite Actual end;reflexivity.
   + repeat lazymatch goal with |- context[@literal_gej_normalize ?alg ?arg] =>
     let Actual:=fresh "Actual" in assert (Actual:@literal_gej_normalize alg arg=inr xy) by exact Normalized;rewrite Actual end.
     cbn [Coqlib.option_map];f_equal;symmetry;exact (taptweak_normalized_x _ _ Normalized).
 - apply Z.ltb_ge in Bound;rewrite (proj2 (Z.leb_le _ _) Bound);reflexivity.
Qed.

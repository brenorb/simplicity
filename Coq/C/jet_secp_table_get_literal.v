(** Original C signed table lookup against the fixed literal lookupTable5.
    Magnitude bounds come from the preceding actual table construction. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp
 C.jet_secp_table_get_execution C.jet_secp_table_get_control C.jet_secp_lookup5_literal
 C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_gej_negate_literal C.jet_secp_curve_literal
 C.jet_secp_rescale_literal C.jet_secp_canonical_normalize C.jet_secp_negate_literal_contract
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_ge_negate literal_fe_negate rescale_field_output canonical_fe_normalize.

Lemma lookup5_decoded_normalized w :
 @canonical_fe_normalize Alg.CoreFunSem (rescale_field_output w)=rescale_field_output w.
Proof.
 apply (toZ_injective (WordToZ 8));rewrite canonical_fe_normalize_numeric,
  canonical_field_order_matches_limb_model,rescale_field_output_value,field_prime_matches_normalizer,
  Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma lookup5_decoded_negative w : mul_small_input_bounds w ->
 rescale_field_output (negate_sep_words w)=@literal_fe_negate Alg.CoreFunSem (rescale_field_output w).
Proof.
 intro Bound;apply (toZ_injective (WordToZ 8)).
 rewrite rescale_field_output_value,field_prime_matches_normalizer,(proj1 (negate_sep_numeric w Bound)),
  literal_curve_negate_numeric,rescale_field_output_value,field_prime_matches_normalizer.
 replace (4*feP-radix_value w) with ((feP-radix_value w)+3*feP) by ring.
 rewrite Z.mod_add by (unfold feP,feR;lia).
 rewrite Zminus_mod_idemp_r;reflexivity.
Qed.

Lemma lookup5_stored_point nib xs ys :
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 let j:=Z.to_nat (lookup5_index nib) in
 (rescale_field_output (xs j),rescale_field_output (if lookup5_negative nib then negate_sep_words (ys j) else ys j))=
 @literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys)).
Proof.
 intro Tight;cbv zeta;pose proof (lookup5_index_range nib) as Index.
 assert (NatIndex:(Z.to_nat (lookup5_index nib)<8)%nat) by lia.
 rewrite literal_lookup5_decoded;cbv zeta;unfold globalz_decoded_points.
 destruct (lookup5_negative nib).
 - change ((rescale_field_output (xs (Z.to_nat (lookup5_index nib))),
    rescale_field_output (negate_sep_words (ys (Z.to_nat (lookup5_index nib)))))=
   (@canonical_fe_normalize Alg.CoreFunSem (rescale_field_output (xs (Z.to_nat (lookup5_index nib)))),
    @literal_fe_negate Alg.CoreFunSem (rescale_field_output (ys (Z.to_nat (lookup5_index nib)))))).
   rewrite lookup5_decoded_normalized,lookup5_decoded_negative by (apply Tight;exact NatIndex);reflexivity.
 - reflexivity.
Qed.

Theorem eval_table_get_lookup5 nib xs ys m bd bt : bd<>bt ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 let j:=Z.to_nat (lookup5_index nib) in
 let outy:=if lookup5_negative nib then negate_sep_words (ys j) else ys j in exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge)
  [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vint (Int.repr (lookup5_digit nib));Vint (Int.repr 5)] E0 mf Vundef /\
 fe_at mf bd 0 (words5 (xs j)) /\ fe_at mf bd 40 (words5 outy) /\
 (rescale_field_output (xs j),rescale_field_output outy)=
  @literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys)) /\
 square_input_bounds (xs j) /\ square_input_bounds outy /\
 Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bd 0 88 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 keeps_permissions m mf /\ lframe (fun b _=>b<>bd) m mf /\ readonly_preserved m mf.
Proof.
 intros Separate Table Bounds Tight FreeT FreeD;cbv zeta.
 pose proof (lookup5_index_range nib) as Index.
 assert (NatIndex:(Z.to_nat (lookup5_index nib)<8)%nat) by lia.
 destruct (Table _ NatIndex) as (X & Y & Flag).
 destruct (Bounds _ NatIndex) as [BX BY].
 rewrite Z2Nat.id in X,Y,Flag by lia.
 rewrite Z.add_0_r in X.
 destruct (eval_table_get_ge (lookup5_negative nib) (lookup5_index nib) m bd bt
  (xs (Z.to_nat (lookup5_index nib))) (ys (Z.to_nat (lookup5_index nib)))
  Index Separate FreeT FreeD X Y Flag)
  as (mf & Call & XF & YF & FlagF & FreeDF & FreeTF & Keep & Frame & Readonly).
 rewrite <-lookup5_digit_source in Call.
 assert (Literal:(rescale_field_output (xs (Z.to_nat (lookup5_index nib))),
  rescale_field_output (if lookup5_negative nib then negate_sep_words (ys (Z.to_nat (lookup5_index nib)))
   else ys (Z.to_nat (lookup5_index nib))))=
  @literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys))).
 { apply lookup5_stored_point;exact Tight. }
 assert (BYF:square_input_bounds (if lookup5_negative nib then negate_sep_words (ys (Z.to_nat (lookup5_index nib)))
  else ys (Z.to_nat (lookup5_index nib)))).
 { destruct (lookup5_negative nib);[apply (proj2 (negate_sep_numeric _ (Tight _ NatIndex)))|exact BY]. }
 exists mf;split;[exact Call|];split;[exact XF|];split;[exact YF|];split;[exact Literal|];
  split;[exact BX|];split;[exact BYF|];split;[exact FlagF|];split;[exact FreeDF|];
  split;[exact FreeTF|];split;[exact Keep|];split;assumption.
Qed.

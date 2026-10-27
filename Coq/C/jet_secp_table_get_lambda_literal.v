(** Original lambda lookup against lookupTable5 followed by ge_scale_lambda.
    The auxiliary X-array relation is an incoming representation invariant;
    its establishment by the real beta-product loop remains separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
 C.jet_secp_table_get_control C.jet_secp_table_get_lambda_execution C.jet_secp_table_get_literal
 C.jet_secp_write_ge_negated_literal
 C.jet_secp_lookup5_literal C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_gej_negate_literal C.jet_secp_beta_spec
 C.jet_secp_canonical_normalize C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
 C.jet_secp_negate_literal_contract C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope term_scope.
Set Default Timeout 10.

(** Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:550, unchanged wiring. *)
Definition literal_ge_scale_lambda {term:Alg.Core.Algebra} : term literal_table_ge literal_table_ge :=
 O (@literal_fe_multiply_beta term) &&& I (@canonical_fe_normalize term).
Local Open Scope Z_scope.
Local Opaque secp_ge literal_fe_multiply_beta canonical_fe_normalize literal_ge_negate rescale_field_output.

Lemma literal_ge_scale_lambda_step (x y : Ty.tySem (Word 8)) :
 @literal_ge_scale_lambda Alg.CoreFunSem (x,y)=
 (@literal_fe_multiply_beta Alg.CoreFunSem x,@canonical_fe_normalize Alg.CoreFunSem y).
Proof. unfold literal_ge_scale_lambda;reflexivity. Qed.

Lemma lookup5_scale_lambda nib xs ys aux :
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 @literal_ge_scale_lambda Alg.CoreFunSem
  (@literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys)))=
 @literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points aux ys)).
Proof.
 intros Match Tight;pose proof (lookup5_index_range nib) as Index.
 assert (NatIndex:(Z.to_nat (lookup5_index nib)<8)%nat) by lia.
 rewrite !literal_lookup5_decoded;cbv zeta;unfold globalz_decoded_points.
 destruct (lookup5_negative nib).
 - rewrite !literal_ge_negate_step,literal_ge_scale_lambda_step.
   rewrite !lookup5_decoded_normalized;apply f_equal2.
   + symmetry;apply Match;exact NatIndex.
   + rewrite <-lookup5_decoded_negative by (apply Tight;exact NatIndex);apply lookup5_decoded_normalized.
 - rewrite literal_ge_scale_lambda_step.
   rewrite lookup5_decoded_normalized;apply f_equal2;[symmetry;apply Match;exact NatIndex|reflexivity].
Qed.

Theorem eval_table_get_lambda_lookup5 nib xs ys aux m bd bt bx : bd<>bt -> bd<>bx ->
 globalz_table_rep m bt xs ys ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 Mem.range_perm m bd 0 88 Cur Freeable ->
 let j:=Z.to_nat (lookup5_index nib) in
 let outy:=if lookup5_negative nib then negate_sep_words (ys j) else ys j in exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_lambda)
 [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;
  Vint (Int.repr (lookup5_digit nib));Vint (Int.repr 5)] E0 mf Vundef /\
 fe_at mf bd 0 (words5 (aux j)) /\ fe_at mf bd 40 (words5 outy) /\
 (rescale_field_output (aux j),rescale_field_output outy)=
  @literal_ge_scale_lambda Alg.CoreFunSem
   (@literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys))) /\
 square_input_bounds (aux j) /\ square_input_bounds outy /\
 Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bd 0 88 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\ keeps_permissions m mf /\
 lframe (fun b _=>b<>bd) m mf /\ readonly_preserved m mf.
Proof.
 intros SepT SepX Table Aux Bounds Tight Match FreeT FreeX FreeD;cbv zeta.
 pose proof (lookup5_index_range nib) as Index.
 assert (NatIndex:(Z.to_nat (lookup5_index nib)<8)%nat) by lia.
 destruct (Table _ NatIndex) as (UnusedX & Y & UnusedFlag).
 pose proof (Aux _ NatIndex) as X.
 rewrite Z2Nat.id in X,Y by lia.
 destruct (eval_table_get_ge_lambda (lookup5_negative nib) (lookup5_index nib) m bd bt bx
  (aux (Z.to_nat (lookup5_index nib))) (ys (Z.to_nat (lookup5_index nib)))
  Index SepT SepX FreeT FreeX FreeD X Y)
  as (mf & Call & XF & YF & FlagF & FreeDF & FreeTF & FreeXF & Keep & Frame & Readonly).
 rewrite <-lookup5_digit_source in Call.
 exists mf;split;[exact Call|];split;[exact XF|];split;[exact YF|];split.
 - exact (eq_trans (lookup5_stored_point nib aux ys Tight)
    (eq_sym (lookup5_scale_lambda nib xs ys aux Match Tight))).
 - split;[apply Bounds;exact NatIndex|];split.
   + destruct (lookup5_negative nib);[apply (proj2 (negate_sep_numeric _ (Tight _ NatIndex)))|].
     apply C.jet_secp_double_coordinate_numeric.double_tight_loose,Tight;exact NatIndex.
   + split;[exact FlagF|];split;[exact FreeDF|];split;[exact FreeTF|];split;[exact FreeXF|];
      split;[exact Keep|];split;assumption.
Qed.

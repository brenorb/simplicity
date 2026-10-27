(** Both original C table calls against the fixed scalarTable5 program.
    The raw extended-addition ratios are kept in the specification; their
    established normalization congruence is used only by the second pass. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_square_columns C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric C.jet_secp_double_literal
 C.jet_secp_field_zero_owned C.jet_secp_field_read_preservation C.jet_secp_slice_permissions
 C.jet_secp_odd_table_loop C.jet_secp_odd_table_body C.jet_secp_odd_table_function
 C.jet_secp_odd_table_firstpass_literal C.jet_secp_odd_table_seed_literal
 C.jet_secp_odd_table_literal_walk C.jet_secp_odd_table_pass1_bridge
 C.jet_secp_scalar_table_literal C.jet_secp_scalar_table_pass2 C.jet_secp_table_field_equiv
 C.jet_secp_globalz_loop C.jet_secp_globalz_function C.jet_secp_globalz_word_walk C.jet_secp_globalz_pass2
 C.jet_secp_rescale_literal C.jet_secp_negate_literal_contract C.jet_secp_canonical_normalize
 C.jet_secp_multiply_literal_spec C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge odd_table_final_state globalz_walk point_mul_words rescale_field_output
 literal_fe_multiply literal_gej_double literal_gej_zinv literal_pass1_8 literal_pass2_8 literal_scalar_table5.

Lemma table_multiply_commute x y :
 @literal_fe_multiply Alg.CoreFunSem (x,y)=@literal_fe_multiply Alg.CoreFunSem (y,x).
Proof. apply (toZ_injective (WordToZ 8));rewrite !literal_multiply_numeric,Z.mul_comm;reflexivity. Qed.

Lemma table_final_product_literal x y z ax ay az :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let sf:=odd_table_final_state x y z in
 let d:Ty.tySem literal_table_gej:=@literal_gej_double Alg.CoreFunSem ((ax,ay),az) in
 let start:Ty.tySem literal_table_gej:=(@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d),az) in
 odd_table_accumulator_bounds sf ->
 rescale_field_output (odd_table_z sf)=
  @canonical_fe_normalize Alg.CoreFunSem (snd (@literal_pass1_8 Alg.CoreFunSem (start,fst d))) ->
 rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z))=
  @literal_fe_multiply Alg.CoreFunSem (snd d,snd (@literal_pass1_8 Alg.CoreFunSem (start,fst d))).
Proof.
 intros BX BY BZ HX HY HZ Finite;cbv zeta;intros (_ & _ & FinalBound) FinalZ.
 pose proof (table_finite_double_literal x y z ax ay az BX BY BZ HX HY HZ Finite) as Double.
 pose proof (f_equal snd Double) as DZ.
 assert (DoubleBound:square_input_bounds (double_output_z_words y z)).
 { unfold double_output_z_words;apply double_tight_loose,double_mul_tight;assumption. }
 pose proof (table_decoded_literal _ _ FinalZ) as FinalResidue.
 apply table_normalized_literal in FinalResidue.
 pose proof (table_decoded_literal _ _ DZ) as DoubleResidue.
 rewrite (rescale_mul_writer _ _ _ _ FinalBound DoubleBound
  ltac:(rewrite field_prime_matches_normalizer;exact FinalResidue)
  ltac:(rewrite field_prime_matches_normalizer;exact DoubleResidue)).
 apply table_multiply_commute.
Qed.

Theorem eval_scalar_table5_calls x y z m br bp bz bo (ax ay az:Ty.tySem (Word 8)) :
 NoDup [br;bp;bz;bo] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bz 0 320 Cur Freeable -> Mem.range_perm m bo 0 40 Cur Freeable ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let sf:=odd_table_final_state x y z in exists m1 mf xf yf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_odd_multiples_table)
  [Vint (Int.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bp Ptrofs.zero] E0 m1 Vundef /\
 Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_ge_table_set_globalz)
  [Vlong (Int64.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero] E0 mf Vundef /\
 globalz_table_rep mf br xf yf /\ globalz_table_bounds xf yf /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 (rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z)),
  globalz_word_vector (globalz_decoded_points xf yf))=
  @literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az) /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
 Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
 Mem.range_perm mf bz 0 320 Cur Freeable /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 keeps_permissions m mf /\ lframe (fun b _=>b<>br /\ b<>bp /\ b<>bz /\ b<>bo) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct BX BY BZ X Y Z Flag FreeT FreeP FreeR FreeO HX HY HZ Finite;cbv zeta.
 assert (Separate:br<>bp /\ br<>bz /\ br<>bo /\ bp<>bz /\ bp<>bo /\ bz<>bo).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Separate as (TP & TR & TO & PR & PO & RO).
 assert (FirstSep:NoDup [br;bp;bz]).
 { repeat constructor;cbn [In];intuition congruence. }
 destruct (odd_table_firstpass_from_inputs x y z m br bp bz bo ax ay az FirstSep BX BY BZ X Y Z Flag
  FreeT FreeP FreeR HX HY HZ Finite) as (FirstTree & FirstZ & FinalBound).
 pose proof (table_final_product_literal x y z ax ay az BX BY BZ HX HY HZ Finite FinalBound FirstZ) as ProductLiteral.
 destruct (eval_ecmult_odd_table_eight x y z m br bp bz bo Distinct BX BY BZ X Y Z Flag FreeT FreeP FreeR FreeO)
  as (m1 & First & Prefix & PrefixBounds & Product & ProductBound & PX & PY & PZ & PFlag &
    FreeT1 & FreeP1 & FreeR1 & FreeO1 & Keep1 & Frame1 & Readonly1).
 set (sf:=odd_table_final_state x y z) in *.
 assert (Table1:globalz_table_rep m1 br (odd_table_xs sf) (odd_table_ys sf)).
 { intros j Range;destruct (Prefix j Range) as (XJ & YJ & FlagJ & RJ);split;
   [rewrite Z.add_0_r;exact XJ|];split;assumption. }
 assert (Ratios1:globalz_ratios_rep m1 bz (odd_table_ratios sf)).
 { intros j Range;exact (proj2 (proj2 (proj2 (Prefix j Range)))). }
 assert (TableBounds:globalz_table_bounds (odd_table_xs sf) (odd_table_ys sf)).
 { intros j Range;destruct (PrefixBounds j Range) as [XJ [YJ RJ]];split;assumption. }
 assert (RatioBounds:globalz_ratios_bounds (odd_table_ratios sf)).
 { intros j Range;exact (proj2 (proj2 (PrefixBounds j Range))). }
 pose proof (eval_ge_table_set_globalz_pass2 (odd_table_xs sf) (odd_table_ys sf) (odd_table_ratios sf)
  m1 br bz TR TableBounds RatioBounds Table1 Ratios1 FreeT1 FreeR1) as SecondCall.
 destruct (globalz_walk 7 (odd_table_xs sf) (globalz_start_ys (odd_table_ys sf))
  (odd_table_ratios sf) (odd_table_ratios sf 7%nat)) as [[xf yf] zf].
 destruct SecondCall as (mf & Second & Decoded & TableF & RatiosF & BoundsF & FreeTF & FreeRF & Keep2 & Frame2 & Readonly2).
 assert (VP:Mem.valid_block m1 bp) by (eapply Mem.perm_valid_block;apply (FreeP1 0);lia).
 assert (ProductF:fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z)))).
 { eapply field_at_lframe;[exact Product|exact Frame2|];intros;split;congruence. }
 assert (PXF:fe_at mf bp 0 (words5 x)) by (eapply field_at_lframe;[exact PX|exact Frame2|];intros;split;congruence).
 assert (PYF:fe_at mf bp 40 (words5 y)) by (eapply field_at_lframe;[exact PY|exact Frame2|];intros;split;congruence).
 assert (PZF:fe_at mf bp 80 (words5 z)) by (eapply field_at_lframe;[exact PZ|exact Frame2|];intros;split;congruence).
 assert (PFlagF:Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 Frame2 Mint32 bp 120 VP);[exact PFlag|intros;split;congruence]. }
 assert (Literal:(rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z)),
  globalz_word_vector (globalz_decoded_points xf yf))=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az)).
 { rewrite literal_scalar_table5_route;cbv zeta;apply f_equal2;[exact ProductLiteral|].
   change (globalz_word_vector (globalz_decoded_points xf yf)=@literal_pass2_8 Alg.CoreFunSem (table_state_tree sf)) in Decoded.
   exact (eq_trans Decoded (table_pass1_consumed _ _ _ FirstTree)). }
 assert (FreePF:Mem.range_perm mf bp 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep2|exact FreeP1]).
 assert (FreeOF:Mem.range_perm mf bo 0 40 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep2|exact FreeO1]).
 exists m1,mf,xf,yf;split;[exact First|];split;[exact Second|];split;[exact TableF|];split;[exact BoundsF|];
  split;[exact ProductF|];split;[exact ProductBound|];split;[exact Literal|];
  split;[exact PXF|];split;[exact PYF|];split;[exact PZF|];split;[exact PFlagF|];
  split;[exact FreeTF|];split;[exact FreePF|];split;[exact FreeRF|];split;[exact FreeOF|];split.
 - eapply keeps_permissions_trans;eassumption.
 - split.
   + eapply lframe_trans;[exact Frame1|].
     eapply lframe_implies;[exact Frame2|];intros old pos (NT & NP & NR & NO) _;split;assumption.
   + eapply preserved_trans;eassumption.
Qed.

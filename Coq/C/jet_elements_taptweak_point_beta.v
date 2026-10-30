(** Original finite/nonzero preprocessing followed by all eight beta products. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_memset_model
 C.jet_secp_strauss_first_loop C.jet_secp_statement_prefix C.jet_secp_generator_preprocess
 C.jet_secp_generator_globalz_call C.jet_secp_canonical_scalar C.jet_secp_split_literal
 C.jet_secp_split_constants C.jet_secp_split_function C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
 C.jet_secp_beta_global C.jet_secp_beta_state C.jet_secp_beta_loop C.jet_secp_beta_loop_step
 C.jet_secp_beta_spec C.jet_secp_square_columns C.jet_secp_point_mul_storage
 C.jet_secp_fe_nv C.jet_secp_odd_table_loop C.jet_secp_odd_table_body C.jet_secp_double_all_calls
 C.jet_secp_odd_table_literal_walk C.jet_secp_scalar_table_literal C.jet_secp_field_zero_owned
 C.jet_secp_globalz_loop C.jet_secp_globalz_word_walk C.jet_secp_globalz_pass2
 C.jet_secp_field_mul_small C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_secp_wnaf_slice_frame C.jet_secp_wnaf_loop
 C.jet_secp_wnaf_pair5 C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge beta_block canonical_scalar_normalize literal_scalar_split_lambda
 odd_table_final_state point_mul_words literal_scalar_table5.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_beta_prepare C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_beta C.jet_elements_taptweak_beta_loop C.jet_elements_taptweak_point_prepare
 C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_split_function C.jet_transport C.jet_transport_locals.
Local Opaque elements_taptweak_ge elements_taptweak_beta_block elements_taptweak_multiplier_block
 elements_taptweak_basis_block elements_taptweak_lambda_block.
Lemma elements_taptweak_strauss_beta_owned_separate m b : elements_taptweak_beta_initialized m ->
 Mem.perm m b 0 Cur Freeable -> b<>elements_taptweak_beta_block.
Proof.
 intros [_ Bounds] Owned Same;subst b.
 destruct (proj1 (Bounds 0 Cur Freeable) Owned) as [_ Order];inversion Order.
Qed.
Theorem exec_elements_taptweak_strauss_point_prepare (Model:memset_model) e le m raw bk br1 br2 bs bp ba bt bx bo bj
 x y z (ax ay az:Ty.tySem (Word 8)) :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 e!_na_1=Some (br1,Tstruct __5826 noattr) -> e!_na_lam=Some (br2,Tstruct __5826 noattr) ->
 e!_Z=Some (bo,Tstruct __5467 noattr) -> e!_tmp=Some (bj,Tstruct __6123 noattr) ->
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_gej_is_infinity=None ->
 e!_secp256k1_scalar_split_lambda=None -> e!_secp256k1_ecmult_wnaf=None ->
 e!_secp256k1_ecmult_odd_multiples_table=None -> e!_secp256k1_ge_table_set_globalz=None ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_const_beta=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_num=Some (Vlong Int64.one) ->
 le!_no=Some (Vlong Int64.zero) -> le!_bits=Some (Vint Int.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 elements_taptweak_split_ready m -> elements_taptweak_beta_initialized m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 (forall b hi,In (b,hi) (strauss_preprocess_storage bk br1 br2 bs bp ba bt bx bo bj) ->
  Mem.range_perm m b 0 hi Cur Freeable) -> NoDup [bk;br1;br2;bs;bp;ba;bt;bx;bo;bj] ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 let sf:=odd_table_final_state x y z in exists lef mf last1 last2 digits1 digits2 xf yf,
 Clight2.exec_stmt elements_taptweak_ge e le m strauss_point_prepare E0 lef mf Out_normal /\
 lef!_np=Some (Vlong Int64.one) /\ lef!_no=Some (Vlong Int64.one) /\ lef!_i=Some (Vint (Int.repr 8)) /\
 lef!_bits=Some (Vint (Int.repr (Z.max (last1+1) (last2+1)))) /\
 0<=Z.max (last1+1) (last2+1)<=129 /\
 wnaf_array_state mf bp 0 129 5 (wnaf5_input_sign (fst (fst halves))) 129 last1 digits1 /\
 wnaf_array_state mf bp 516 129 5 (wnaf5_input_sign (fst (snd halves))) 129 last2 digits2 /\
 0<=last1+1<=129 /\ 0<=last2+1<=129 /\
 Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1))) /\
 Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1))) /\
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (fst halves))*digits1 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (snd halves))*digits2 (Z.of_nat i)) (seq 0 129)) /\
 globalz_table_rep mf bt xf yf /\ globalz_table_bounds xf yf /\
 (forall k,(k<8)%nat -> mul_small_input_bounds (yf k)) /\
 beta_aux_prefix mf bx xf 8 /\
 (forall k,(k<8)%nat -> square_input_bounds (beta_aux_values xf k)) /\
 (forall k,(k<8)%nat -> rescale_field_output (beta_aux_values xf k)=
  @literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xf k))) /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 (rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z)),
  globalz_word_vector (globalz_decoded_points xf yf))=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\ Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 (forall b hi,In (b,hi) (strauss_preprocess_storage bk br1 br2 bs bp ba bt bx bo bj) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\ elements_taptweak_split_ready mf /\ elements_taptweak_beta_initialized mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun old pos=>elements_taptweak_split_function_frame bk br1 br2 old pos /\
  wnaf_slice_outside bp 0 260 old pos /\ old<>bt /\ old<>bj /\ old<>bx /\ old<>bo /\ old<>elements_taptweak_beta_block) m mf /\
 (forall id,~In id [_np;_no;_i;_bits;_t'1;_t'2;_t'3;_t'4;_t'5;_t'30;_t'31;_t'32;_t'33;_t'36;_t'37;
   _t'38;_t'39;_t'40;_t'41;_t'42;_t'43;_t'44;_t'45;_t'46;_t'47] -> lef!id=le!id).
Proof.
 intros Domain BoundEnv Low High LocalZ LocalTmp ZeroSymbol FlagSymbol SplitSymbol WnafSymbol OddSymbol GlobalSymbol MulSymbol ConstSymbol
  NA A State Num No Bits PS PT PX Ready Init Input Nonzero BX BY BZ X Y Z Flag Owned Separate HX HY HZ Finite;
  cbv zeta.
 assert (Different:forall b,In b [bk;bs;bp;ba;bo;bj] -> b<>bt /\ b<>bx).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;
   intros b Slot;cbn [In] in Slot;intuition congruence. }
 assert (TX:bt<>bx).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (NoBeta:forall b hi,In (b,hi) (strauss_preprocess_storage bk br1 br2 bs bp ba bt bx bo bj) -> b<>elements_taptweak_beta_block).
 { intros b hi Slot;apply (elements_taptweak_strauss_beta_owned_separate m b Init);apply (Owned b hi Slot 0).
   split;[reflexivity|exact (strauss_preprocess_storage_positive bk br1 br2 bs bp ba bt bx bo bj b hi Slot)]. }
 destruct (exec_elements_taptweak_strauss_preprocess_finite Model e le m raw bk br1 br2 bs bp ba bt bx bo bj x y z ax ay az Domain BoundEnv
  Low High LocalZ LocalTmp ZeroSymbol FlagSymbol SplitSymbol WnafSymbol OddSymbol GlobalSymbol
  NA A State Num No Bits PS PT PX Ready Input Nonzero BX BY BZ X Y Z Flag Owned Separate HX HY HZ Finite)
  as (lp & mp & last1 & last2 & digits1 & digits2 & xf & yf & Prepare & NPP & NoP & Max & MaxBound &
   Array1 & Array2 & Bound1 & Bound2 & Count1 & Count2 & Literal1 & Literal2 & Table & TableBound & TightY &
   Product & ProductBound & TableLiteral & XP & YP & ZP & FlagP & PSP & PTP & PXP & InputP &
   OwnedP & ReadyP & KeepP & ReadonlyP & FrameP & OtherP).
 assert (InitP:elements_taptweak_beta_initialized mp) by (eapply elements_taptweak_beta_initialized_preserved;[exact Init|exact ReadonlyP]).
 assert (StateP:lp!_state=Some (Vptr bs Ptrofs.zero)).
 { rewrite OtherP by (cbn [In];intuition discriminate);exact State. }
 assert (FreeS:Mem.range_perm mp bs 0 24 Cur Freeable) by
  (apply OwnedP;clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (FreeT:Mem.range_perm mp bt 0 704 Cur Freeable) by
  (apply OwnedP;clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (FreeX:Mem.range_perm mp bx 0 320 Cur Freeable) by
  (apply OwnedP;clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (SB:bs<>elements_taptweak_beta_block) by (apply (NoBeta bs 24);clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (TB:bt<>elements_taptweak_beta_block) by (apply (NoBeta bt 704);clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (XB:bx<>elements_taptweak_beta_block) by (apply (NoBeta bx 320);clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 destruct (exec_elements_taptweak_beta_auxiliary_one e lp xf yf mp bs bt bx
  (proj1 (Different bs ltac:(clear;cbn [In];tauto))) (proj2 (Different bs ltac:(clear;cbn [In];tauto))) SB TX TB XB
  MulSymbol ConstSymbol StateP NoP PXP PTP Table ltac:(intros k K;exact (proj1 (TableBound k K)))
  FreeS FreeT FreeX InitP)
  as (lef & mf & Beta & NPF & IF & OtherB & Memory & BetaBound & BetaLiteral).
 destruct Memory as (TableF & AuxF & PXF & PTF & FSF & FTF & FXF & InitF & KeepB & ReadonlyB & FrameB).
 assert (Protected:forall b hi,In (b,hi) (strauss_preprocess_storage bk br1 br2 bs bp ba bt bx bo bj) ->
  In b [bk;bs;bp;ba;bo;bj] -> forall pos,elements_taptweak_beta_aux_loop_frame bt bx b pos).
 { intros b hi Slot Member pos;destruct (Different b Member) as [T Xb];unfold elements_taptweak_beta_aux_loop_frame.
   split;[exact Xb|];split;[exact T|exact (NoBeta b hi Slot)]. }
 assert (BP:forall pos,elements_taptweak_beta_aux_loop_frame bt bx bp pos).
 { apply (Protected bp 1040);[clear;unfold strauss_preprocess_storage;cbn [In];tauto|clear;cbn [In];tauto]. }
 assert (BS:forall pos,elements_taptweak_beta_aux_loop_frame bt bx bs pos).
 { apply (Protected bs 24);[clear;unfold strauss_preprocess_storage;cbn [In];tauto|clear;cbn [In];tauto]. }
 assert (BA:forall pos,elements_taptweak_beta_aux_loop_frame bt bx ba pos).
 { apply (Protected ba 128);[clear;unfold strauss_preprocess_storage;cbn [In];tauto|clear;cbn [In];tauto]. }
 assert (BO:forall pos,elements_taptweak_beta_aux_loop_frame bt bx bo pos).
 { apply (Protected bo 40);[clear;unfold strauss_preprocess_storage;cbn [In];tauto|clear;cbn [In];tauto]. }
 assert (BK:forall pos,elements_taptweak_beta_aux_loop_frame bt bx bk pos).
 { apply (Protected bk 32);[clear;unfold strauss_preprocess_storage;cbn [In];tauto|clear;cbn [In];tauto]. }
 assert (A1F:wnaf_array_state mf bp 0 129 5
  (wnaf5_input_sign (fst (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))) 129 last1 digits1).
 { eapply wnaf_array_slice_lframe;[exact Array1|exact FrameB|intros;apply BP]. }
 assert (A2F:wnaf_array_state mf bp 516 129 5
  (wnaf5_input_sign (fst (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))) 129 last2 digits2).
 { eapply wnaf_array_slice_lframe;[exact Array2|exact FrameB|intros;apply BP]. }
 assert (FP:Mem.range_perm mp bp 0 1040 Cur Freeable) by (apply OwnedP;clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (VP:Mem.valid_block mp bp) by (eapply Mem.perm_valid_block;apply (FP 0);clear;lia).
 assert (VS:Mem.valid_block mp bs) by (eapply Mem.perm_valid_block;apply (FreeS 0);clear;lia).
 assert (Count1F:Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1)))).
 { rewrite (proj1 FrameB Mint32 bp 1032 VP ltac:(intros;apply BP));exact Count1. }
 assert (Count2F:Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1)))).
 { rewrite (proj1 FrameB Mint32 bp 1036 VP ltac:(intros;apply BP));exact Count2. }
 assert (PSF:Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero)).
 { rewrite (proj1 FrameB Mptr bs 16 VS ltac:(intros;apply BS));exact PSP. }
 assert (ProductF:fe_at mf bo 0 (words5 (point_mul_words (odd_table_z (odd_table_final_state x y z)) (double_output_z_words y z)))).
 { eapply field_at_lframe;[exact Product|exact FrameB|exact BO]. }
 assert (XF:fe_at mf ba 0 (words5 x)) by (eapply field_at_lframe;[exact XP|exact FrameB|exact BA]).
 assert (YF:fe_at mf ba 40 (words5 y)) by (eapply field_at_lframe;[exact YP|exact FrameB|exact BA]).
 assert (ZF:fe_at mf ba 80 (words5 z)) by (eapply field_at_lframe;[exact ZP|exact FrameB|exact BA]).
 assert (FAP:Mem.range_perm mp ba 0 128 Cur Freeable) by (apply OwnedP;clear;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (VA:Mem.valid_block mp ba) by (eapply Mem.perm_valid_block;apply (FAP 0);clear;lia).
 assert (FlagF:Mem.load Mint32 mf ba 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameB Mint32 ba 120 VA ltac:(intros;apply BA));exact FlagP. }
 assert (InputF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact InputP|exact FrameB|exact BK]. }
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact KeepP|exact KeepB]).
 exists lef,mf,last1,last2,digits1,digits2,xf,yf;split.
 - unfold strauss_point_prepare;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prepare|exact Beta].
 - split;[exact NPF|];split;[rewrite OtherB by discriminate;exact NoP|];split;[exact IF|];split;
   [rewrite OtherB by discriminate;exact Max|];split;[exact MaxBound|];
   split;[exact A1F|];split;[exact A2F|];split;[exact Bound1|];split;[exact Bound2|];
   split;[exact Count1F|];split;[exact Count2F|];split;[exact Literal1|];split;[exact Literal2|];
   split;[exact TableF|];split;[exact TableBound|];split;[exact TightY|];split;[exact AuxF|];
   split;[exact BetaBound|];split;[exact BetaLiteral|];split;[exact ProductF|];split;[exact ProductBound|];
   split;[exact TableLiteral|];split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact FlagF|];
   split;[exact PSF|];split;[exact PTF|];split;[exact PXF|];split;[exact InputF|];split.
   + intros b hi Slot pos Range;apply Keep,(Owned b hi Slot);exact Range.
   + split;[eapply elements_taptweak_split_readonly;[exact ReadyP|exact ReadonlyB]|];split;[exact InitF|];split;[exact Keep|];split.
     * eapply preserved_trans;[exact ReadonlyP|exact ReadonlyB].
     * split.
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact FrameP|].
             intros b pos (S & W & T & J & Xb & O & _) _;
              split;[exact S|];split;[exact W|];repeat split;assumption.
          ++ eapply lframe_implies;[exact FrameB|intros b pos (_ & _ & T & _ & Xb & _ & B) _;unfold elements_taptweak_beta_aux_loop_frame;repeat split;assumption].
       -- intros id Outside;rewrite OtherB by (clear -Outside;cbn [In] in Outside;intuition congruence).
          apply OtherP;clear -Outside;cbn [In] in Outside|-*;tauto.
Qed.

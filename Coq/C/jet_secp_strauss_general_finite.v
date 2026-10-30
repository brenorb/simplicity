(** Whole original Strauss call with a finite nonzero point: actual
    preprocessing, arbitrary generator scalar, private allocations and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_strauss_point_loop C.jet_secp_strauss_digit_guard
 C.jet_secp_generator_digit_control C.jet_secp_generator_loop_control
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_wnaf5_literal C.jet_secp_strauss_wnaf_calls
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_double_loose_literal
 C.jet_secp_double_literal C.jet_secp_mixed_xy_literal C.jet_secp_strauss_program
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge rescale_field_output literal_gej_double literal_strauss_step.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_scale_iteration.


Require Import C.jet_secp_strauss_scale_loop C.jet_secp_negate_literal_contract C.jet_secp_globalz_word_walk C.jet_secp_generator_point_stage C.jet_secp_generator_entry C.jet_secp_generator_final C.jet_secp_strauss_final_literal
 C.jet_secp_double_var_owned C.jet_secp_gej_infinity_owned C.jet_secp_literal_infinity C.jet_secp_curve_literal C.jet_secp_generator_loop_literal.
Local Opaque literal_fe_multiply literal_gej_infinity.

Require Import C.jet_clight_readonly_frame C.jet_secp_strauss_generator_zero C.jet_secp_strauss_digit_index C.jet_secp_strauss_scale_point_stage C.jet_secp_strauss_scale_literal
 C.jet_secp_strauss_zero_generator C.jet_secp_generator_main C.jet_secp_generator_digit_index
 C.jet_secp_strauss_complete_program C.jet_secp_split_literal C.jet_secp_wnaf5_input
 C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_loop C.jet_memset_model.
Local Opaque literal_strauss_body literal_scalar_table5 literal_scalar_split_lambda.



From Coq Require Import ZArith List.
From compcert Require Import Coqlib Memory Values.
Require Import C.jet_sx_mem C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_scale_function C.jet_secp_strauss_general_main C.jet_secp_generator_pair_general C.jet_secp_generator_globals.
Require Import C.jet_secp_split_constants C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_beta_global C.jet_clight_readonly_frame C.jet_secp_strauss_beta_prepare
 C.jet_secp_strauss_first_loop C.jet_secp_generator_globalz_call C.jet_secp_generator_preprocess
 C.jet_secp_statement_prefix C.jet_secp_point_mul_storage C.jet_secp_field_zero_owned
 C.jet_secp_odd_table_body C.jet_secp_odd_table_loop C.jet_secp_double_all_calls
 C.jet_secp_strauss_scale_main C.jet_secp_beta_state C.jet_secp_beta_loop_step
 C.jet_secp_odd_table_literal_walk C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support C.jet_secp_generator_initialize
 C.jet_secp_generator_function C.jet_secp_split_function C.jet_secp_wnaf_slice_frame C.jet_secp_beta_loop.

Definition strauss_linear_outer_storage br bk ba bs bp bt bx bng : list (block*Z) :=
 [(br,128);(bk,32);(ba,128);(bs,24);(bp,1040);(bt,704);(bx,320);(bng,32)].
Lemma strauss_linear_outer_size_positive br bk ba bs bp bt bx bng b hi :
 In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) -> 0<hi.
Proof.
 intro Slot;assert (Sizes:In hi (map (@snd block Z) (strauss_linear_outer_storage br bk ba bs bp bt bx bng))).
 { apply in_map_iff;exists (b,hi);split;[reflexivity|exact Slot]. }
 change (In hi [128;32;128;24;1040;704;320;32]) in Sizes;cbn [In] in Sizes;intuition lia.
Qed.

Require Import C.jet_clight_forward.

Theorem eval_strauss_general_finite_flag_forward (Model:memset_model)
 (raw ng ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx bng :
 (forall h,generator_table_state h m) -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx;bng] ->
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),ng) /\
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx;bng]) m mf /\
 (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (fst (@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az))))=false ->
  Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))) /\ mem_forward m mf.
Proof.
 intros Tables Ready Beta OuterSeparate Outer Input InputNG Nonzero BX BY BZ X Y Z Flag HX HY HZ Finite PS PT PX.
 assert (OldValid:forall b,In b [br;bk;ba;bs;bp;bt;bx;bng] -> Mem.valid_block m b).
 { intros b Member;change (In b (map (@fst block BinNums.Z) (strauss_linear_outer_storage br bk ba bs bp bt bx bng))) in Member.
   apply in_map_iff in Member;destruct Member as [[b' hi] [Eq Slot]];cbn [fst] in Eq;subst b'.
   eapply Mem.perm_valid_block;apply (Outer b hi Slot 0);split;[reflexivity|].
   eapply strauss_linear_outer_size_positive;exact Slot. }
 assert (VG:Mem.valid_block m bng).
 { apply OldValid;clear;cbn [In];tauto. }
 destruct (strauss_entry_and_initialize m bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero))
  as (mi & mp & bd & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Init & Denominator & Separate & Old & Owned & FrameI & KeepI & ReadI).
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 pose (le:=strauss_entry_temps bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero)).
 pose (li:=generator_initial_temps le).
 assert (Different:forall b,In b [br;bk;ba;bs;bp;bt;bx;bng] ->
  ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]).
 { intros b Slot;apply Old,OldValid;exact Slot. }
 assert (PrepSeparate:NoDup [bk;bn;bl;bs;bp;ba;bt;bx;bz;bj]).
 { assert (OldSix:NoDup [bk;bs;bp;ba;bt;bx]).
   { clear -OuterSeparate;repeat rewrite NoDup_cons_iff in OuterSeparate;
     repeat rewrite NoDup_cons_iff;cbn [In] in *;intuition congruence. }
   assert (FreshFour:NoDup [bn;bl;bz;bj]).
   { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;
     repeat rewrite NoDup_cons_iff;cbn [In] in *;intuition congruence. }
   assert (Union:NoDup ([bk;bs;bp;ba;bt;bx]++[bn;bl;bz;bj])).
   { apply strauss_nodup_append;[exact OldSix|exact FreshFour|].
     intros b Slot Inside;apply (Different b);[clear -Slot;cbn [In] in *;tauto|
      clear -Inside;cbn [In] in *;tauto]. }
   eapply NoDup_incl_NoDup with (l:=[bk;bs;bp;ba;bt;bx]++[bn;bl;bz;bj]).
   - exact Union.
   - cbn;lia.
   - intros b;cbn [app In];tauto. }
 assert (MainSeparate:NoDup [br;bs;bp;bt;bx;bd;bz;b0;b128;bw0;bw128;bj;bn;bl;bng]).
 { assert (Union:NoDup ([br;bs;bp;bt;bx;bng]++[bd;bz;b0;b128;bw0;bw128;bj;bn;bl])).
   { apply strauss_nodup_append.
     - clear -OuterSeparate;repeat rewrite NoDup_cons_iff in OuterSeparate;
       repeat rewrite NoDup_cons_iff;cbn [In] in *;intuition congruence.
     - exact Separate.
     - intros b Slot;apply Different;cbn [In] in Slot|-*;tauto. }
   eapply NoDup_incl_NoDup with (l:=[br;bs;bp;bt;bx;bng]++[bd;bz;b0;b128;bw0;bw128;bj;bn;bl]).
   - exact Union.
   - cbn;lia.
   - intros b;cbn [app In];tauto. }
 assert (PrepOwned:forall b hi,In (b,hi) (strauss_preprocess_storage bk bn bl bs bp ba bt bx bz bj) ->
  Mem.range_perm mp b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [strauss_preprocess_storage In] in Slot.
   repeat match type of Slot with _ \/ _ =>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst b hi.
   all:first [solve [apply Owned;clear;cbn [generator_local_storage In];tauto]|
    eapply curve_keep_free;[clear;lia|apply Outer;clear;cbn [strauss_linear_outer_storage In];tauto|exact FrameI|intros;exact I]]. }
 assert (Saved:forall chunk b ofs v,Mem.load chunk m b ofs=Some v -> Mem.load chunk mp b ofs=Some v).
 { intros chunk b ofs v Load;rewrite (proj1 FrameI chunk b ofs);[exact Load| |intros;exact I].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (InputI:scalar_at mp bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (InputNGI:scalar_at mp bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact FrameI|intros;exact I]. }
 assert (TablesI:forall h,generator_table_state h mp) by
  (eapply generator_tables_readonly;[exact Tables|exact ReadI]).
 assert (XI:fe_at mp ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameI|intros;exact I]).
 assert (YI:fe_at mp ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameI|intros;exact I]).
 assert (ZI:fe_at mp ba 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact FrameI|intros;exact I]).
 assert (FlagI:Mem.load Mint32 mp ba 120=Some (Vint Int.zero)) by (apply Saved;exact Flag).
 assert (PSI:Mem.load Mptr mp bs 16=Some (Vptr bp Ptrofs.zero)) by (apply Saved;exact PS).
 assert (PTI:Mem.load Mptr mp bs 8=Some (Vptr bt Ptrofs.zero)) by (apply Saved;exact PT).
 assert (PXI:Mem.load Mptr mp bs 0=Some (Vptr bx Ptrofs.zero)) by (apply Saved;exact PX).
 assert (ReadyI:split_constants_ready mp) by (eapply split_constants_readonly;[exact Ready|exact ReadI]).
 assert (BetaI:beta_initialized mp) by (eapply beta_initialized_preserved;[exact Beta|exact ReadI]).
 assert (NAI:li!_na=Some (Vptr bk Ptrofs.zero)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (AI:li!_a=Some (Vptr ba Ptrofs.zero)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (SI:li!_state=Some (Vptr bs Ptrofs.zero)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (NumI:li!_num=Some (Vlong Int64.one)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (NoI:li!_no=Some (Vlong Int64.zero)) by (unfold li,generator_initial_temps;apply PTree.gss).
 assert (BitsI:li!_bits=Some (Vint Int.zero)).
 { unfold li,generator_initial_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 destruct (exec_strauss_point_prepare Model e li mp raw bk bn bl bs bp ba bt bx bz bj x y z ax ay az
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  NAI AI SI NumI NoI BitsI PSI PTI PXI ReadyI BetaI InputI Nonzero BX BY BZ XI YI ZI FlagI
  PrepOwned PrepSeparate HX HY HZ Finite)
  as (lp & ms & last1 & lastlam & digits1 & digitslam & xf & yf & Prepare & NP & NoP & IP & BitsP & BitsBound &
   A1 & AL & B1 & BL & C1 & CL & L1 & LL & Table & Bounds & Tight & Aux & AuxBounds & AuxLiteral &
   Inv & InvBounds & Context & XP & YP & ZP & FlagP & PSP & PTP & PXP & InputP &
   OwnedP & ReadyP & BetaP & KeepP & ReadP & FrameP & OtherP).
 assert (RP:lp!_r=Some (Vptr br Ptrofs.zero)).
 { rewrite OtherP by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (SP:lp!_state=Some (Vptr bs Ptrofs.zero)) by (rewrite OtherP by (clear;cbn [In];intuition discriminate);exact SI).
 assert (NGP:lp!_ng=Some (Vptr bng Ptrofs.zero)).
 { rewrite OtherP by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (TablesP:forall h,generator_table_state h ms) by
  (eapply generator_tables_readonly;[exact TablesI|exact ReadP]).
 assert (FrameNG:lframe (fun b _=>b=bng) mp ms).
 { assert (OutsideOld:~In bng [br;bk;ba;bs;bp;bt;bx]).
   { pose proof (NoDup_remove_2 [br;bk;ba;bs;bp;bt;bx] [] bng OuterSeparate) as Apart.
     cbn [app] in Apart;exact Apart. }
   assert (OutsideFresh:~In bng [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by
    (apply Different;clear;cbn [In];tauto).
   eapply strauss_restore_readonly_exceptions with (exceptions:=strauss_readonly_blocks);[|exact ReadP|].
   - eapply lframe_implies;[exact FrameP|].
     intros b pos [Same OutsideRO] Valid;subst b;unfold split_function_frame,wnaf_slice_outside.
     clear -OutsideOld OutsideFresh OutsideRO;cbn [strauss_readonly_blocks In] in *;intuition congruence.
   - apply strauss_readonly_blocks_not_writable;assumption. }
 assert (InputNGP:scalar_at ms bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNGI|exact FrameNG|intros;reflexivity]. }
 assert (LocalP:forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos P;apply KeepP;apply (Owned b hi Slot);exact P. }
 assert (OuterP:forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos P;apply KeepP,KeepI;apply (Outer b hi Slot);exact P. }
 destruct (exec_strauss_general_main_flag_forward Model lp ms bng br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl
  raw ng ((ax,ay),az) xf yf (beta_aux_values xf)
  (point_mul_words (odd_table_z (odd_table_final_state x y z)) (double_output_z_words y z))
  last1 lastlam digits1 digitslam MainSeparate RP SP NoP BitsP NGP InputNGP
  (OuterP bng 32 ltac:(clear;cbn [strauss_linear_outer_storage In];tauto)) TablesP PSP PTP PXP C1 CL A1 AL L1 LL
  Table Bounds Tight Aux AuxBounds AuxLiteral InvBounds Inv Context
  (OuterP br 128 ltac:(clear;cbn [strauss_linear_outer_storage In];tauto))
  (OuterP bt 704 ltac:(clear;cbn [strauss_linear_outer_storage In];tauto))
  (OuterP bx 320 ltac:(clear;cbn [strauss_linear_outer_storage In];tauto)) LocalP)
  as (lef & mu & ox & oy & oz & Main & RF & XO & YO & ZO & BXO & BYO & BZO & Literal & FreeRU &
   FreeTU & FreeXU & LocalU & KeepM & TablesU & FrameM & ConditionalMain & ForwardMain).
 assert (KeepU:keeps_permissions m mu) by
  (eapply keeps_permissions_trans;[exact KeepI|];eapply keeps_permissions_trans;[exact KeepP|exact KeepM]).
 assert (PrepFrame:lframe
  (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx;bng] /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) mp ms).
 { eapply strauss_restore_readonly_exceptions with (exceptions:=strauss_readonly_blocks);[|exact ReadP|].
   - eapply lframe_implies;[exact FrameP|].
     intros b pos [[OutsideOld OutsideFresh] OutsideRO] Valid.
     unfold split_function_frame,wnaf_slice_outside.
     clear -OutsideOld OutsideFresh OutsideRO.
     cbn [strauss_readonly_blocks In] in *;intuition congruence.
   - apply strauss_readonly_blocks_not_writable;assumption. }
 destruct (free_list_exists
  [(bw128,0,516);(bw0,0,516);(bd,0,88);(bj,0,128);(bz,0,40);(b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)] mu)
  as (mf & Released & UnchangedF).
 - pose proof Separate as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
   clear -Distinct;cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;clear -LocalU Slot;cbn [In] in Slot.
   repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst;apply LocalU;clear;cbn [generator_local_storage In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) mu mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside Valid;clear -Outside;cbn [map fst In] in *;intuition congruence. }
   assert (OutsideR:~In br [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Different;clear;cbn [In];tauto).
   assert (OutsideG:~In bng [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VG).
   assert (XF:fe_at mf br 0 (words5 ox)) by (eapply field_at_lframe;[exact XO|exact FrameF|intros;exact OutsideR]).
   assert (YF:fe_at mf br 40 (words5 oy)) by (eapply field_at_lframe;[exact YO|exact FrameF|intros;exact OutsideR]).
   assert (ZF:fe_at mf br 80 (words5 oz)) by (eapply field_at_lframe;[exact ZO|exact FrameF|intros;exact OutsideR]).
   assert (ConditionalF:
    Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
     (fst (@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az))))=false ->
    Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
   { intro NonzeroInv;rewrite (proj1 FrameF Mint32 br 120).
     - apply ConditionalMain.
       pose proof (f_equal fst Context) as SharedValue;cbn [fst] in SharedValue.
       rewrite SharedValue;exact NonzeroInv.
     - eapply Mem.perm_valid_block;apply (FreeRU 0);lia.
     - intros pos Range;exact OutsideR. }
   assert (OuterF:forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
    Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot;eapply curve_keep_free with (P:=fun b _=>~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) (m:=mu).
     - eapply strauss_linear_outer_size_positive;exact Slot.
     - intros pos P;apply KeepU;apply (Outer b hi Slot);exact P.
     - exact FrameF.
     - intros pos;apply Old.
       eapply Mem.perm_valid_block;apply (Outer b hi Slot 0);split;[reflexivity|eapply strauss_linear_outer_size_positive;exact Slot]. }
   assert (TablesF:forall h,generator_table_state h mf).
   { eapply generator_tables_readonly;[exact TablesU|eapply freelist_preserved;exact Released]. }
   assert (Frame:lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx;bng]) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ ~In b [br;bk;ba;bs;bp;bt;bx;bng]).
     - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
       eapply lframe_trans.
       + eapply lframe_implies;[exact PrepFrame|intros b pos [Valid Outside] _;split;[exact Outside|apply Old;exact Valid]].
       + eapply lframe_trans.
         * eapply lframe_implies;[exact FrameM|intros b pos [Valid Outside] _;split;
            [clear -Outside;cbn [In] in Outside;intuition congruence|];split;
            [apply Old;exact Valid|clear -Outside;cbn [In] in Outside;intuition congruence]].
         * eapply lframe_implies;[exact FrameF|intros b pos [Valid Outside] _;apply Old;exact Valid].
     - intros b pos Outside Valid;split;assumption. }
   assert (PrepareAll:Clight2.exec_stmt secp_ge e le mi generator_prepare_non_generator E0 lp ms Out_normal).
   { rewrite generator_prepare_non_generator_source;eapply exec_statement_prefix_then_last;
      [exact Init|apply strauss_prepare_reassociate;exact Prepare]. }
   assert (Forward:mem_forward m mf).
   { eapply mem_forward_trans;[exact (proj1 ReadI)|].
     eapply mem_forward_trans;[exact (proj1 ReadP)|].
     eapply mem_forward_trans;[exact ForwardMain|eapply freelist_forward;exact Released]. }
   exists mf,ox,oy,oz;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mu) (out:=Out_normal).
     * exact Entry.
     * rewrite generator_body_main_source;eapply exec_statement_prefix_then_last;[exact PrepareAll|exact Main].
     * reflexivity.
     * unfold e;rewrite generator_local_blocks;exact Released.
   + split;[exact XF|];split;[exact YF|];split;[exact ZF|];
     split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];
     split;[exact Literal|];split;[exact OuterF|];split;[exact TablesF|];split;[exact Frame|];split;[exact ConditionalF|exact Forward].
Qed.

Theorem eval_strauss_general_finite_flag (Model:memset_model)
 (raw ng ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx bng :
 (forall h,generator_table_state h m) -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx;bng] ->
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),ng) /\
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx;bng]) m mf /\
 (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (fst (@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az))))=false ->
  Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
Proof.
 intros Tables Ready Beta OuterSeparate Outer Input InputNG Nonzero BX BY BZ X Y Z Flag HX HY HZ Finite PS PT PX.
 destruct (eval_strauss_general_finite_flag_forward Model raw ng ax ay az x y z m br bk ba bs bp bt bx bng
  Tables Ready Beta OuterSeparate Outer Input InputNG Nonzero BX BY BZ X Y Z Flag HX HY HZ Finite PS PT PX)
  as (mf & ox & oy & oz & Exec & XO & YO & ZO & BXO & BYO & BZO & Literal &
   OuterOut & TablesOut & Frame & Conditional & Forward).
 exists mf,ox,oy,oz;repeat first [assumption|split].
Qed.


Theorem eval_strauss_general_finite (Model:memset_model)
 (raw ng ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx bng :
 (forall h,generator_table_state h m) -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx;bng] ->
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),ng) /\
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx;bng]) m mf.
Proof.
 intros Tables Ready Beta OuterSeparate Outer Input InputNG Nonzero BX BY BZ X Y Z Flag HX HY HZ Finite PS PT PX.
 destruct (eval_strauss_general_finite_flag Model raw ng ax ay az x y z m br bk ba bs bp bt bx bng
  Tables Ready Beta OuterSeparate Outer Input InputNG Nonzero BX BY BZ X Y Z Flag HX HY HZ Finite PS PT PX)
  as (mf & ox & oy & oz & Exec & XO & YO & ZO & BXO & BYO & BZO & Literal &
   OuterOut & TablesOut & Frame & Conditional).
 exists mf,ox,oy,oz;repeat first [assumption|split].
Qed.

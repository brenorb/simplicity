(** Original ecmult wrapper with arbitrary ordinary and generator scalars. *)
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


Require Import C.jet_secp_strauss_scale_function.
Require Import C.jet_secp_strauss_scale_main C.jet_secp_split_constants C.jet_secp_beta_global
 C.jet_secp_beta_state C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
 C.jet_secp_odd_table_literal_walk C.jet_secp_literal_gej_predicate C.jet_secp_statement_prefix.

Require Import C.jet_secp_ecmult_generator C.jet_secp_ecmult_entry C.jet_secp_ecmult_state
 C.jet_clight_forward C.jet_clight_readonly.
Require Import C.jet_secp_strauss_general_function C.jet_secp_strauss_general_finite
 C.jet_secp_generator_globals C.jet_secp_generator_pair_general.
Local Opaque literal_off_curve_linear_combination_1.

Theorem eval_ecmult_general (Model:memset_model)
 (raw ng ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bng :
 (forall h,generator_table_state h m) -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bng] ->
 (forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128);(bng,32)] ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az))))) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero]
  E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,((ax,ay),az)),ng) /\
 (forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128);(bng,32)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (forall h,generator_table_state h mf) /\ lframe (fun b _=>~In b [br;bk;ba;bng]) m mf.
Proof.
 intros Tables Ready Beta Separate Owned Input InputNG BX BY BZ X Y Z Flag HX HY HZ.
 assert (Valid:forall b,In b [br;bk;ba;bng] -> Mem.valid_block m b).
 { intros b [Same|[Same|[Same|[Same|[]]]]];subst b;eapply Mem.perm_valid_block;
   first [exact (Owned br 128 ltac:(clear;cbn [In];tauto) 0 ltac:(clear;lia))|
    exact (Owned bk 32 ltac:(clear;cbn [In];tauto) 0 ltac:(clear;lia))|
    exact (Owned ba 128 ltac:(clear;cbn [In];tauto) 0 ltac:(clear;lia))|
    exact (Owned bng 32 ltac:(clear;cbn [In];tauto) 0 ltac:(clear;lia))]. }
 destruct (ecmult_entry_and_state m (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero))
  as (mi & ms & bx & bt & bp & bs & Entry & Setup & PX & PT & PS &
   PrivateSeparate & Fresh & PrivateOwned & UnchangedS).
 pose (e:=ecmult_env bx bt bp bs).
 pose (le:=ecmult_temps (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero)).
 assert (FrameS:lframe (fun _ _=>True) m ms) by (apply lframe_unchanged;exact UnchangedS).
 assert (ReadS:readonly_preserved m ms).
 { split.
   - eapply mem_forward_trans;[eapply clight_entry2_forward;exact Entry|].
     exact (proj1 (clight_exec_forward secp_ge) _ _ _ _ _ _ _ _ Setup).
   - eapply Mem.unchanged_on_implies;[exact UnchangedS|intros;exact I]. }
 assert (TablesS:forall h,generator_table_state h ms) by (eapply generator_tables_readonly;[exact Tables|exact ReadS]).
 assert (ReadyS:split_constants_ready ms) by (eapply split_constants_readonly;[exact Ready|exact ReadS]).
 assert (BetaS:beta_initialized ms) by (eapply beta_initialized_preserved;[exact Beta|exact ReadS]).
 assert (Different:forall b,In b [br;bk;ba;bng] -> ~In b [bx;bt;bp;bs]).
 { intros b Slot;apply Fresh,Valid;exact Slot. }
 assert (AllSeparate:NoDup [br;bk;ba;bs;bp;bt;bx;bng]).
 { assert (Union:NoDup ([br;bk;ba;bng]++[bs;bp;bt;bx])).
   { apply strauss_nodup_append;[exact Separate| |].
     - clear -PrivateSeparate;repeat rewrite NoDup_cons_iff in PrivateSeparate;
        repeat rewrite NoDup_cons_iff;cbn [In] in *;intuition congruence.
     - intros b Slot;pose proof (Different b Slot) as Outside;clear -Outside;cbn [In] in *;tauto. }
   eapply NoDup_incl_NoDup with (l:=[br;bk;ba;bng]++[bs;bp;bt;bx]).
   - exact Union.
   - cbn;lia.
   - intros b;cbn [app In];tauto. }
 assert (AllOwned:forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [strauss_linear_outer_storage In] in Slot;
   repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst b hi.
   all:first [solve [apply PrivateOwned;clear;cbn [In];tauto]|
     eapply curve_keep_free;[clear;lia|apply Owned;clear;cbn [In];tauto|exact FrameS|intros;exact I]]. }
 assert (InputS:scalar_at ms bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact Input|exact FrameS|intros;exact I]. }
 assert (InputNGS:scalar_at ms bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact FrameS|intros;exact I]. }
 assert (XS:fe_at ms ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameS|intros;exact I]).
 assert (YS:fe_at ms ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameS|intros;exact I]).
 assert (ZS:fe_at ms ba 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact FrameS|intros;exact I]).
 assert (FlagS:Mem.load Mint32 ms ba 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)))))).
 { rewrite (proj1 FrameS Mint32 ba 120);[exact Flag|apply Valid;clear;cbn [In];tauto|intros;exact I]. }
 destruct (eval_strauss_general Model raw ng ax ay az x y z ms br bk ba bs bp bt bx bng
  TablesS ReadyS BetaS AllSeparate AllOwned InputS InputNGS BX BY BZ XS YS ZS FlagS HX HY HZ PS PT PX)
  as (mc & ox & oy & oz & Strauss & XO & YO & ZO & BXO & BYO & BZO & Literal & OwnedC & TablesC & FrameC).
 assert (Call:Clight2.exec_stmt secp_ge e le ms ecmult_strauss_call E0 le mc Out_normal).
 { rewrite ecmult_strauss_call_source;eapply exec_curve_call with
   (vargs:=[Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
    Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs with (v1:=Vptr bs Ptrofs.zero).
     + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
     + reflexivity.
     + eapply eval_Econs with (v1:=Vptr br Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|].
       eapply eval_Econs with (v1:=Vint Int.one);[constructor|reflexivity|].
       eapply eval_Econs with (v1:=Vptr ba Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|].
       eapply eval_Econs with (v1:=Vptr bk Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|].
       eapply eval_Econs with (v1:=Vptr bng Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Strauss. }
 destruct (free_list_exists [(bs,0,24);(bx,0,320);(bp,0,1040);(bt,0,704)] mc)
  as (mf & Released & UnchangedF).
 - clear -PrivateSeparate;repeat rewrite NoDup_cons_iff in PrivateSeparate;cbn [In] in PrivateSeparate;
   cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;clear -OwnedC Slot;cbn [In] in Slot.
   repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst b lo hi;apply OwnedC;clear;cbn [strauss_linear_outer_storage In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bx;bt;bp;bs]) mc mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside V;clear -Outside;cbn [map fst In] in *;tauto. }
   assert (OutsideR:~In br [bx;bt;bp;bs]) by (apply Different;clear;cbn [In];tauto).
   assert (XF:fe_at mf br 0 (words5 ox)) by (eapply field_at_lframe;[exact XO|exact FrameF|intros;exact OutsideR]).
   assert (YF:fe_at mf br 40 (words5 oy)) by (eapply field_at_lframe;[exact YO|exact FrameF|intros;exact OutsideR]).
   assert (ZF:fe_at mf br 80 (words5 oz)) by (eapply field_at_lframe;[exact ZO|exact FrameF|intros;exact OutsideR]).
   assert (OwnedF:forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128);(bng,32)] ->
    Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot;eapply curve_keep_free with (m:=mc) (P:=fun b _=>~In b [bx;bt;bp;bs]).
     - clear -Slot;destruct Slot as [Same|[Same|[Same|[Same|[]]]]];injection Same;intros;subst;lia.
     - apply OwnedC;unfold strauss_linear_outer_storage;cbn [In] in Slot|-*;tauto.
     - exact FrameF.
     - intros pos;apply Different;clear -Slot;cbn [In] in Slot|-*;intuition congruence. }
   assert (GlobalF:(forall h,generator_table_state h mf)).
   { eapply generator_tables_readonly;[exact TablesC|eapply freelist_preserved;exact Released]. }
   assert (Frame:lframe (fun b _=>~In b [br;bk;ba;bng]) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ ~In b [br;bk;ba;bng]).
     - eapply lframe_trans;[eapply lframe_implies;[exact FrameS|intros;exact I]|].
       eapply lframe_trans.
       + eapply lframe_implies;[exact FrameC|].
         intros b pos [V Outside] _;pose proof (Fresh b V) as Private;
          clear -Outside Private;cbn [In] in *;tauto.
       + eapply lframe_implies;[exact FrameF|intros b pos [V Outside] _;apply Fresh;exact V].
     - intros b pos Outside V;split;assumption. }
   exists mf,ox,oy,oz;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=le) (m1:=mi) (m2:=mc) (out:=Out_normal).
     * exact Entry.
     * rewrite ecmult_body_source;eapply exec_statement_prefix_then_last;[exact Setup|exact Call].
     * reflexivity.
     * unfold e;rewrite ecmult_local_blocks;exact Released.
   + split;[exact XF|];split;[exact YF|];split;[exact ZF|];
     split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];
     split;[exact Literal|];split;[exact OwnedF|];split;assumption.
Qed.

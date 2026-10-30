(** Whole original Strauss call when the point contribution is skipped.
    The generator scalar is arbitrary; allocations, preprocessing, wNAF
    clearing under memset_model, point execution and all frees are derived. *)
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


Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_strauss_skip
 C.jet_secp_generator_function C.jet_secp_scalar_add_reader_support
 C.jet_secp_generator_initialize C.jet_secp_generator_globalz_call
 C.jet_secp_statement_prefix C.jet_secp_canonical_scalar
 C.jet_secp_generator_globals C.jet_secp_wnaf_memset C.jet_clight_forward.
Require Import C.jet_secp_generate_program C.jet_secp_generator_main C.jet_secp_point_set_bit C.jet_secp_strauss_scale_function.
Local Opaque literal_generate.

Require Import C.jet_clight_forward.

Theorem eval_strauss_general_skipped_flag_forward (Model:memset_model) value (ng:Ty.tySem (Word 8)) m br bk ba bs bt bx bng :
 (forall h,generator_table_state h m) -> 0<=value<2^256 ->
 scalar_at m bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 scalar_at m bng 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 br<>bng -> Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\
 fe_at mf br 40 (words5 oy) /\
 fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_generate Alg.CoreFunSem ng /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>b<>br /\ b<>bng) m mf /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\ mem_forward m mf.
Proof.
 intros Tables Range Input Skip PT PX InputNG Different FreeR FreeNG.
 assert (VR:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FreeR 0);clear;lia).
 assert (VG:Mem.valid_block m bng) by (eapply Mem.perm_valid_block;apply (FreeNG 0);clear;lia).
 destruct (strauss_entry_and_initialize m bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero))
  as (mi & mp & bd & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Init & Denominator & Separate & Old & Owned & FrameI & KeepI & ReadI).
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 pose (le:=strauss_entry_temps bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero)).
 pose (li:=generator_initial_temps le).
 assert (Saved:forall chunk b ofs v,Mem.load chunk m b ofs=Some v -> Mem.load chunk mp b ofs=Some v).
 { intros chunk b ofs v Load;rewrite (proj1 FrameI chunk b ofs);[exact Load| |intros;exact I].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (InputP:scalar_at mp bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value))).
 { eapply scalar_at_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (SkipP:value=0 \/ Mem.load Mint32 mp ba 120=Some (Vint Int.one)).
 { destruct Skip as [Zero|Flag];[left;exact Zero|right;apply Saved;exact Flag]. }
 assert (PTP:Mem.load Mptr mp bs 8=Some (Vptr bt Ptrofs.zero)) by (apply Saved;exact PT).
 assert (PXP:Mem.load Mptr mp bs 0=Some (Vptr bx Ptrofs.zero)) by (apply Saved;exact PX).
 assert (NAI:li!_na=Some (Vptr bk Ptrofs.zero)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (AI:li!_a=Some (Vptr ba Ptrofs.zero)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (NumI:li!_num=Some (Vlong Int64.one)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (NoI:li!_no=Some (Vlong Int64.zero)) by (unfold li,generator_initial_temps;apply PTree.gss).
 assert (StateI:li!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 destruct (exec_strauss_no_points e li mp value bk ba bs bt bx eq_refl eq_refl eq_refl
  NAI AI NumI NoI StateI Range InputP SkipP PTP PXP)
  as (ms & SkipCall & NP & NoS & Other & UnchangedS & FrameS & KeepS & ReadS).
 pose (ls:=strauss_no_points_temps li value (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 assert (RS:ls!_r=Some (Vptr br Ptrofs.zero)).
 { unfold ls;rewrite Other by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (BitsS:ls!_bits=Some (Vint Int.zero)).
 { unfold ls;rewrite Other by (clear;cbn [In];intuition discriminate).
   unfold li,generator_initial_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 assert (NGS:ls!_ng=Some (Vptr bng Ptrofs.zero)).
 { unfold ls;rewrite Other by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (InputNGS:scalar_at ms bng 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[|exact FrameS|intros;exact I].
   eapply scalar_at_lframe;[exact InputNG|exact FrameI|intros;exact I]. }
 assert (TablesS:forall h,generator_table_state h ms).
 { intro h;apply (generator_table_state_unchanged h m ms);[|apply Tables].
   eapply Mem.unchanged_on_implies.
   - exact (proj2 (preserved_trans m mp ms ReadI ReadS)).
   - intros b pos At Valid;subst b;split;[exact Valid|].
     apply (readonly_bounds_not_writable _ _ _ _ (proj2 (Tables h))). }
 assert (DenominatorS:fe_at ms bz 0 (words5 (point_set_bit_words Datatypes.true))).
 { eapply field_at_lframe;[exact Denominator|exact FrameS|intros;exact I]. }
 assert (FreeNGS:Mem.range_perm ms bng 0 32 Cur Freeable).
 { intros pos P;apply KeepS,KeepI,FreeNG;exact P. }
 assert (FreeRS:Mem.range_perm ms br 0 128 Cur Freeable).
 { intros pos P;apply KeepS,KeepI,FreeR;exact P. }
 assert (OwnedS:forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos P;apply KeepS;apply (Owned b hi Slot);exact P. }
 assert (OutsideR:~In br [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VR).
 assert (OutsideG:~In bng [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VG).
 assert (MainSep:NoDup [br;bd;bz;b0;b128;bw0;bw128;bj;bn;bl;bng]).
 { assert (Union:NoDup ([br;bng]++[bd;bz;b0;b128;bw0;bw128;bj;bn;bl])).
   { apply strauss_nodup_append.
     - repeat constructor;cbn [In];intuition congruence.
     - exact Separate.
     - intros b [Same|[Same|[]]];subst b;assumption. }
   eapply NoDup_incl_NoDup with (l:=[br;bng]++[bd;bz;b0;b128;bw0;bw128;bj;bn;bl]).
   - exact Union.
   - cbn;lia.
   - intros b;cbn [app In];tauto. }
 destruct (exec_generator_main_stage_forward ls ms ng br bng bd bz b0 b128 bw0 bw128 bj bn bl
  MainSep TablesS RS NGS NoS BitsS InputNGS DenominatorS FreeRS FreeNGS OwnedS
  ltac:(intros high ma mm local Alloc OwnedW;exact (generate_memset_steps Model ma mm local
   (if high then b128 else b0) (if high then bw128 else bw0) Alloc OwnedW)))
  as (lef & mu & ox & oy & oz & Main & PRF & X & Y & Z & Flag & FreeRU & FreeNGU &
   OwnedU & BX & BY & BZ & Literal & FrameM & ForwardMain).
 assert (TablesU:forall h,generator_table_state h mu).
 { intro h;pose proof (TablesS h) as [Table Bounds];pose proof Table as [Valid _].
   assert (Outside:generator_table_block h<>br /\
    ~In (generator_table_block h) [bd;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
    generator_table_block h<>bng).
   { split.
     - intro Same;rewrite Same in Bounds.
       destruct (proj1 (Bounds 0 Cur Freeable) (FreeRS 0 ltac:(clear;lia))) as [_ Order];inversion Order.
     - split.
       + intro Member.
         assert (Slot:exists hi,In (generator_table_block h,hi)
           (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) /\ 0<hi).
         { clear -Member;cbn [In] in Member;cbn [generator_local_storage In].
           repeat match type of Member with _ \/ _=>destruct Member as [Member|Member] end;
           try contradiction.
           all:rewrite <-Member;first
            [solve [exists 88;split;[tauto|lia]]|solve [exists 40;split;[tauto|lia]]|
             solve [exists 32;split;[tauto|lia]]|solve [exists 516;split;[tauto|lia]]|
             solve [exists 128;split;[tauto|lia]]]. }
         destruct Slot as (hi & Slot & Positive).
         destruct (proj1 (Bounds 0 Cur Freeable)
          (OwnedS _ hi Slot 0 ltac:(clear -Positive;lia))) as [_ Order];inversion Order.
       + intro Same;rewrite Same in Bounds.
         destruct (proj1 (Bounds 0 Cur Freeable) (FreeNGS 0 ltac:(clear;lia))) as [_ Order];inversion Order. }
   pose proof (generator_table_rep_lframe h ms mu _ Table FrameM ltac:(intro;exact Outside)) as Rep.
   split;[exact Rep|].
   eapply readonly_bounds_transport;[exact Valid|exact Bounds| |exact (proj1 (proj2 Rep))].
   exact ForwardMain. }
 destruct (free_list_exists
  [(bw128,0,516);(bw0,0,516);(bd,0,88);(bj,0,128);(bz,0,40);(b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)] mu)
  as (mf & Released & UnchangedF).
 - pose proof Separate as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
   clear -Distinct;cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;clear -OwnedU Slot;cbn [In] in Slot.
   repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst;apply OwnedU;clear;cbn [generator_local_storage In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) mu mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside Valid;clear -Outside;cbn [map fst In] in *;intuition congruence. }
   assert (XF:fe_at mf br 0 (words5 ox)).
   { eapply field_at_lframe;[exact X|exact FrameF|intros;exact OutsideR]. }
   assert (YF:fe_at mf br 40 (words5 oy)).
   { eapply field_at_lframe;[exact Y|exact FrameF|intros;exact OutsideR]. }
   assert (ZF:fe_at mf br 80 (words5 oz)).
   { eapply field_at_lframe;[exact Z|exact FrameF|intros;exact OutsideR]. }
   assert (FlagF:Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
    (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
   { rewrite (proj1 FrameF Mint32 br 120).
     - exact Flag.
     - eapply Mem.perm_valid_block;apply (FreeRU 0);lia.
     - intros pos RangeHere;exact OutsideR. }
   assert (FreeRF:Mem.range_perm mf br 0 128 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FreeRU|exact FrameF|intros;exact OutsideR]. }
   assert (FreeNGF:Mem.range_perm mf bng 0 32 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FreeNGU|exact FrameF|intros;exact OutsideG]. }
   assert (TablesF:forall h,generator_table_state h mf).
   { intro h;apply (generator_table_state_unchanged h mu mf);[|apply TablesU].
     eapply Mem.unchanged_on_implies;[exact (proj2 (freelist_preserved _ _ _ Released))|].
     intros b pos At Valid;subst b;split;[exact Valid|].
     apply (readonly_bounds_not_writable _ _ _ _ (proj2 (TablesU h))). }
   assert (Frame:lframe (fun b _=>b<>br /\ b<>bng) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>br /\ b<>bng).
     - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
       eapply lframe_trans;[eapply lframe_implies;[exact FrameS|intros;exact I]|].
       eapply lframe_trans.
       + eapply lframe_implies;[exact FrameM|].
         intros b pos [Valid [NotR NotG]] _;split;[exact NotR|];split;[apply Old;exact Valid|exact NotG].
       + eapply lframe_implies;[exact FrameF|intros b pos [Valid _] _;apply Old;exact Valid].
     - intros b pos [NotR NotG] Valid;split;[exact Valid|];split;assumption. }
   assert (Prepare:Clight2.exec_stmt secp_ge e le mi generator_prepare_non_generator E0 ls ms Out_normal).
   { rewrite generator_prepare_non_generator_source;eapply exec_statement_prefix_then_last;[exact Init|exact SkipCall]. }
   assert (Forward:mem_forward m mf).
   { eapply mem_forward_trans;[exact (proj1 ReadI)|].
     eapply mem_forward_trans;[exact (proj1 ReadS)|].
     eapply mem_forward_trans;[exact ForwardMain|eapply freelist_forward;exact Released]. }
   exists mf,ox,oy,oz;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mu) (out:=Out_normal).
     * exact Entry.
     * rewrite generator_body_main_source;eapply exec_statement_prefix_then_last;[exact Prepare|exact Main].
     * reflexivity.
     * unfold e;rewrite generator_local_blocks;exact Released.
   + split;[exact XF|];split;[exact YF|];split;[exact ZF|];
     split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Literal|];
     split;[exact FreeRF|];split;[exact FreeNGF|];split;[exact TablesF|];split;[exact Frame|];split;[exact FlagF|exact Forward].
Qed.

Theorem eval_strauss_general_skipped_flag (Model:memset_model) value (ng:Ty.tySem (Word 8)) m br bk ba bs bt bx bng :
 (forall h,generator_table_state h m) -> 0<=value<2^256 ->
 scalar_at m bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 scalar_at m bng 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 br<>bng -> Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\
 fe_at mf br 40 (words5 oy) /\
 fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_generate Alg.CoreFunSem ng /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>b<>br /\ b<>bng) m mf /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))).
Proof.
 intros Tables Range Input Skip PT PX InputNG Different FreeR FreeNG.
 destruct (eval_strauss_general_skipped_flag_forward Model value ng m br bk ba bs bt bx bng
  Tables Range Input Skip PT PX InputNG Different FreeR FreeNG)
  as (mf & ox & oy & oz & Exec & XO & YO & ZO & BX & BY & BZ & Literal &
   FR & FG & TablesOut & Frame & OutputFlag & Forward).
 exists mf,ox,oy,oz;repeat first [assumption|split].
Qed.

Theorem eval_strauss_general_skipped (Model:memset_model) value (ng:Ty.tySem (Word 8)) m br bk ba bs bt bx bng :
 (forall h,generator_table_state h m) -> 0<=value<2^256 ->
 scalar_at m bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 scalar_at m bng 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 br<>bng -> Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\
 fe_at mf br 40 (words5 oy) /\
 fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_generate Alg.CoreFunSem ng /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>b<>br /\ b<>bng) m mf.
Proof.
 intros Tables Range Input Skip PT PX InputNG Different FreeR FreeNG.
 destruct (eval_strauss_general_skipped_flag Model value ng m br bk ba bs bt bx bng
  Tables Range Input Skip PT PX InputNG Different FreeR FreeNG)
  as (mf & ox & oy & oz & Exec & XO & YO & ZO & BX & BY & BZ & Literal &
   FR & FG & TablesOut & Frame & OutputFlag).
 exists mf,ox,oy,oz;repeat first [assumption|split].
Qed.

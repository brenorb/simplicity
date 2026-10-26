(** Complete original odd-table body for its eight-entry ecmult caller:
    initialization, all seven mixed additions and the final Z product.
    Local allocation and cleanup, and the canonical table bridge, remain
    separate obligations. No intermediate execution or output is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_odd_table_head C.jet_secp_odd_table_seed C.jet_secp_odd_table_loop C.jet_secp_odd_table_iteration
 C.jet_secp_curve_statements C.jet_secp_statement_prefix C.jet_secp_ge_zinv_arithmetic
 C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric C.jet_secp_square_columns
 C.jet_secp_field_slice_product C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions
 C.jet_secp_field_read_preservation C.jet_secp_curve_frame C.jet_secp_slice_permissions
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge odd_table_walk point_mul_words.

Definition odd_table_initial_state x y z := odd_table_seed_state
 (ge_zinv_x_words x (double_output_z_words y z))
 (ge_zinv_y_words y (double_output_z_words y z)) z (double_output_z_words y z).
Definition odd_table_final_state x y z := odd_table_walk 7 1 (odd_table_initial_state x y z)
 (double_output_x_words x y) (double_output_y_words x y).
Definition odd_table_final_product := snd (split_statement_last (fn_body f_secp256k1_ecmult_odd_multiples_table)).
Definition odd_table_body_frame (br bp bz bo bd ba bg:block) (b:block) (_:Z) :=
 b<>br /\ b<>bp /\ b<>bz /\ b<>bo /\ b<>bd /\ b<>ba /\ b<>bg.

Lemma odd_table_body_source : fn_body f_secp256k1_ecmult_odd_multiples_table=
 statement_sequence odd_table_head_statements (statement_sequence odd_table_seed_statements
  (Ssequence (Ssequence (Sset _i (Econst_int Int.one tint)) odd_table_loop) odd_table_final_product)).
Proof. reflexivity. Qed.
Lemma odd_table_final_product_source : odd_table_final_product=
 curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [Etempvar _z (tptr curve_fe_type);odd_table_local_field_address _ai _z;odd_table_local_field_address _d _z].
Proof. reflexivity. Qed.
Local Ltac separate Distinct := clear -Distinct;
 repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence.

Theorem exec_odd_table_body e le x y z m br bp bz bo bd ba bg :
 NoDup [br;bp;bz;bo;bd;ba;bg] ->
 e!_d=Some (bd,Tstruct __6123 noattr) -> e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_d_ge=Some (bg,curve_ge_type) ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_ge_set_xy=None -> e!_secp256k1_ge_set_gej_zinv=None ->
 e!_secp256k1_gej_set_ge=None -> e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_fe_mul=None ->
 le!_n=Some (Vint (Int.repr 8)) -> le!_a=Some (Vptr bp Ptrofs.zero) ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) -> le!_z=Some (Vptr bo Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bz 0 320 Cur Freeable -> Mem.range_perm m bo 0 40 Cur Freeable ->
 Mem.range_perm m bd 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bg 0 88 Cur Freeable ->
 let sf:=odd_table_final_state x y z in exists lef mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_ecmult_odd_multiples_table) E0 lef mf Out_normal /\
 lef!_i=Some (Vint (Int.repr 8)) /\ (forall id,id<>_i -> lef!id=le!id) /\
 odd_table_prefix mf br bz 8 sf /\ odd_table_prefix_bounds 8 sf /\
 odd_table_accumulator mf ba sf /\ odd_table_accumulator_bounds sf /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
 Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
 Mem.range_perm mf bz 0 320 Cur Freeable /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 Mem.range_perm mf bd 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bg 0 88 Cur Freeable /\
 keeps_permissions m mf /\ lframe (odd_table_body_frame br bp bz bo bd ba bg) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct D AI DG DoubleGlobal XYGlobal ZinvGlobal SetGlobal AddGlobal MulGlobal N A Table Ratios Out
  BX BY BZ X Y Z Flag FreeT FreeP FreeR FreeO FreeD FreeA FreeG;cbv zeta.
 assert (HeadSep:NoDup [br;bp;bd;bg]) by
  (repeat constructor;cbn [In];separate Distinct).
 destruct (exec_odd_table_head e le x y z m br bp bd bg HeadSep D DG DoubleGlobal XYGlobal ZinvGlobal A Table
   BX BY BZ X Y Z Flag FreeT FreeP FreeD FreeG)
  as (mh & Head & TX & TY & TFlag & PX & PY & PZ & PFlag & GX & GY & GFlag & DZ &
    BTX & BTY & BDX & BDY & BDZ & FreeTH & FreePH & FreeDH & FreeGH & KeepH & FrameH & ReadonlyH).
 assert (FreeAH:Mem.range_perm mh ba 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepH|exact FreeA]).
 assert (FreeRH:Mem.range_perm mh bz 0 320 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepH|exact FreeR]).
 assert (SeedSep:NoDup [ba;br;bp;bd;bz]) by (repeat constructor;cbn [In];separate Distinct).
 destruct (exec_odd_table_seed e le _ _ z _ mh ba br bp bd bz SeedSep AI D SetGlobal Table A Ratios
   BTX BTY BZ BDZ TX TY TFlag PZ DZ FreeAH FreeTH FreePH FreeDH FreeRH)
  as (ms & Seed & SeedFields & PrefixS & PrefixBoundsS & AccS & AccBoundsS & PZS & DZS &
    FreeAS & FreeTS & FreePS & FreeDS & FreeRS & KeepS & FrameS & ReadonlyS).
 assert (LoopSep:NoDup [br;ba;bg;bz]) by (repeat constructor;cbn [In];separate Distinct).
 assert (GXS:fe_at ms bg 0 (words5 (double_output_x_words x y))).
 { eapply field_at_lframe;[exact GX|exact FrameS|];intros;split;[separate Distinct|left;separate Distinct]. }
 assert (GYS:fe_at ms bg 40 (words5 (double_output_y_words x y))).
 { eapply field_at_lframe;[exact GY|exact FrameS|];intros;split;[separate Distinct|left;separate Distinct]. }
 assert (GFlagS:Mem.load Mint32 ms bg 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameS Mint32 bg 80);[exact GFlag| |].
   - eapply Mem.perm_valid_block;apply (FreeGH 0);lia.
   - intros;split;[separate Distinct|left;separate Distinct]. }
 assert (FreeGS:Mem.range_perm ms bg 0 88 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepS|exact FreeGH]).
 set (le1:=PTree.set _i (Vint Int.one) le).
 assert (Other1:forall id,id<>_i -> le1!id=le!id) by
  (intros id Different;unfold le1;apply PTree.gso;exact Different).
 destruct (exec_odd_table_loop 7 1 ltac:(lia) eq_refl e le1 ms br ba bg bz (odd_table_initial_state x y z)
   (double_output_x_words x y) (double_output_y_words x y) LoopSep AI DG AddGlobal XYGlobal
   ltac:(rewrite Other1 by discriminate;exact Table) ltac:(rewrite Other1 by discriminate;exact Ratios)
   ltac:(unfold le1;apply PTree.gss) ltac:(rewrite Other1 by discriminate;exact N)
   PrefixS PrefixBoundsS AccS AccBoundsS BDX BDY GXS GYS GFlagS FreeTS FreeAS FreeGS FreeRS)
  as (lef & ml & Loop & IF & Others & PrefixL & PrefixBoundsL & AccL & AccBoundsL & GXL & GYL & GFlagL &
    FreeTL & FreeAL & FreeGL & FreeRL & KeepL & FrameL & ReadonlyL).
 assert (DZL:fe_at ml bd 80 (words5 (double_output_z_words y z))).
 { eapply field_at_lframe;[exact DZS|exact FrameL|];intros;unfold odd_table_loop_frame;
    repeat split;separate Distinct. }
 destruct AccL as (AXL & AYL & AZL & AFlagL);destruct AccBoundsL as (BAX & BAY & BAZ).
 assert (KeepHS:keeps_permissions m ms) by (eapply keeps_permissions_trans;[exact KeepH|exact KeepS]).
 assert (KeepHSL:keeps_permissions m ml) by (eapply keeps_permissions_trans;[exact KeepHS|exact KeepL]).
 assert (FreeOL:Mem.range_perm ml bo 0 40 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepHSL|exact FreeO]).
 destruct (eval_field_slice_product _ _ ml bo 0 ba 80 bd 80 BAZ BDZ
   ltac:(left;separate Distinct) ltac:(left;separate Distinct) ltac:(left;separate Distinct)
   ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia)
   ltac:(apply freeable_range_writable;exact FreeOL) AZL DZL)
  as (mf & Mul & Product & AZF & DZF & ProductValue & ProductBound & KeepM & FrameM).
 assert (AccF:odd_table_accumulator mf ba (odd_table_final_state x y z)).
 { split.
   - eapply curve_keep_field_range;[reflexivity|exact AXL|exact FrameM|];intros pos Range;
      split;[left;separate Distinct|];split;[right;left;lia|left;separate Distinct].
   - split.
     + eapply curve_keep_field_range;[reflexivity|exact AYL|exact FrameM|];intros pos Range;
        split;[left;separate Distinct|];split;[right;left;lia|left;separate Distinct].
     + split;[exact AZF|].
       rewrite (proj1 FrameM Mint32 ba 120);[exact AFlagL| |].
       * eapply Mem.perm_valid_block;apply (FreeAL 0);lia.
       * intros pos Range;change (120<=pos<120+4) in Range;
          split;[left;separate Distinct|];split;[right;right;lia|left;separate Distinct]. }
 assert (PrefixF:odd_table_prefix mf br bz 8 (odd_table_final_state x y z)).
 { intros j Bound;destruct (PrefixL j Bound) as (XJ & YJ & FlagJ & RJ);split.
   - eapply field_at_lframe;[exact XJ|exact FrameM|];intros;repeat split;left;separate Distinct.
   - split.
     + eapply field_at_lframe;[exact YJ|exact FrameM|];intros;repeat split;left;separate Distinct.
     + split.
       * rewrite (proj1 FrameM Mint32 br (88*Z.of_nat j+80));[exact FlagJ| |].
         -- eapply Mem.perm_valid_block;apply (FreeTL 0);lia.
         -- intros;repeat split;left;separate Distinct.
       * eapply field_at_lframe;[exact RJ|exact FrameM|];intros;repeat split;left;separate Distinct. }
 assert (SourceFrame:lframe (fun b _=>b=bp) mh mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameS|];intros b pos -> Valid;split;[separate Distinct|left;separate Distinct].
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameL|];intros b pos -> Valid;unfold odd_table_loop_frame;repeat split;separate Distinct.
     + eapply lframe_implies;[exact FrameM|];intros b pos -> Valid;repeat split;left;separate Distinct. }
 assert (PXF:fe_at mf bp 0 (words5 x)) by (eapply field_at_lframe;[exact PX|exact SourceFrame|];intros;reflexivity).
 assert (PYF:fe_at mf bp 40 (words5 y)) by (eapply field_at_lframe;[exact PY|exact SourceFrame|];intros;reflexivity).
 assert (PZF:fe_at mf bp 80 (words5 z)) by (eapply field_at_lframe;[exact PZ|exact SourceFrame|];intros;reflexivity).
 assert (PFlagF:Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 SourceFrame Mint32 bp 120);[exact PFlag| |intros;reflexivity].
   eapply Mem.perm_valid_block;apply (FreePH 0);lia. }
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact KeepHSL|exact KeepM]).
 assert (FreeTF:Mem.range_perm mf br 0 704 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeT]).
 assert (FreePF:Mem.range_perm mf bp 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeP]).
 assert (FreeRF:Mem.range_perm mf bz 0 320 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeR]).
 assert (FreeOF:Mem.range_perm mf bo 0 40 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeO]).
 assert (FreeDF:Mem.range_perm mf bd 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeD]).
 assert (FreeAF:Mem.range_perm mf ba 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeA]).
 assert (FreeGF:Mem.range_perm mf bg 0 88 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeG]).
 assert (Frame:lframe (odd_table_body_frame br bp bz bo bd ba bg) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameH|];intros b pos (NT & NP & NR & NO & ND & NA & NG) Valid;
      repeat split;assumption.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameS|];intros b pos (NT & NP & NR & NO & ND & NA & NG) Valid;
        split;[exact NA|left;exact NR].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FrameL|];intros b pos (NT & NP & NR & NO & ND & NA & NG) Valid;
          unfold odd_table_loop_frame;repeat split;assumption.
       * eapply lframe_implies;[exact FrameM|];intros b pos (NT & NP & NR & NO & ND & NA & NG) Valid;
          repeat split;left;assumption. }
 assert (Readonly:readonly_preserved m mf).
 { eapply preserved_trans;[exact ReadonlyH|];eapply preserved_trans;[exact ReadonlyS|];
    eapply preserved_trans;[exact ReadonlyL|].
   eapply (secp_closed_function_preserved f_secp256k1_fe_mul);[reflexivity|reflexivity|exact Mul]. }
 assert (FinalRun:Clight2.exec_stmt secp_ge e lef ml odd_table_final_product E0 lef mf Out_normal).
 { rewrite odd_table_final_product_source;eapply exec_curve_call with
    (vargs:=[Vptr bo Ptrofs.zero;Vptr ba (Ptrofs.repr 80);Vptr bd (Ptrofs.repr 80)]) (v:=Vundef).
   - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   - exact MulGlobal.
   - eapply eval_Econs;[apply eval_Etempvar;rewrite Others by discriminate;rewrite Other1 by discriminate;exact Out|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_field_address with (b:=ba) (delta:=80);[right;right;left;reflexivity|exact AI]|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_field_address with (b:=bd) (delta:=80);[right;right;left;reflexivity|exact D]|reflexivity|constructor].
   - exact Mul. }
 exists lef,mf;split.
 - rewrite odd_table_body_source;eapply exec_statement_prefix_then_last;[exact Head|].
   eapply exec_statement_prefix_then_last;[exact SeedFields|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lef) (m1:=ml);[|exact FinalRun].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=ms);[constructor;constructor|exact Loop].
 - split;[exact IF|];split.
   + intros id Different;rewrite Others by exact Different;apply Other1;exact Different.
   + repeat (first [assumption|split]).
Qed.

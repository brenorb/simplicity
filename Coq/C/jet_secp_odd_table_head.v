(** Original odd-table initialization through its first affine table entry:
    double the input, construct d_ge and scale the input by d.z. No inverse,
    on-curve, nonzero-Y or assumed helper execution is required. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_statements C.jet_secp_statement_prefix C.jet_secp_gej_infinity_layout
 C.jet_secp_double_var_separate C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric
 C.jet_secp_ge_set_xy C.jet_secp_ge_zinv_indexed_function C.jet_secp_ge_zinv_arithmetic
 C.jet_secp_ge_zinv_factor C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_secp_curve_frame C.jet_secp_slice_permissions
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition odd_table_head_statements := firstn 4
 (fst (split_statement_last (fn_body f_secp256k1_ecmult_odd_multiples_table))).
Definition odd_table_head := statement_sequence odd_table_head_statements Sskip.
Definition odd_table_local_point name := Eaddrof (Evar name (Tstruct __6123 noattr))
 (tptr (Tstruct __6123 noattr)).
Definition odd_table_local_field name fid := Efield (Evar name (Tstruct __6123 noattr)) fid curve_fe_type.
Definition odd_table_local_field_address name fid := Eaddrof (odd_table_local_field name fid) (tptr curve_fe_type).
Definition odd_table_first_entry := Ebinop Oadd (Etempvar _pre_a (tptr curve_ge_type))
 (Econst_int Int.zero tint) (tptr curve_ge_type).
Definition odd_table_head_frame (br bp bd bg:block) (b:block) (_:Z) := b<>br /\ b<>bp /\ b<>bd /\ b<>bg.

Lemma odd_table_head_source : odd_table_head=
 Ssequence (Sloop Sskip Sbreak)
 (Ssequence (curve_call _secp256k1_gej_double_var f_secp256k1_gej_double_var None
   [odd_table_local_point _d;Etempvar _a (tptr (Tstruct __6123 noattr));
     Ecast (Econst_int Int.zero tint) (tptr tvoid)])
 (Ssequence (curve_call _secp256k1_ge_set_xy f_secp256k1_ge_set_xy None
   [Eaddrof (Evar _d_ge curve_ge_type) (tptr curve_ge_type);
     odd_table_local_field_address _d _x;odd_table_local_field_address _d _y])
 (Ssequence (curve_call _secp256k1_ge_set_gej_zinv f_secp256k1_ge_set_gej_zinv None
   [odd_table_first_entry;Etempvar _a (tptr (Tstruct __6123 noattr));odd_table_local_field_address _d _z]) Sskip))).
Proof. reflexivity. Qed.
Lemma eval_odd_table_local_field e le m name fid delta b :
 In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> e!name=Some (b,Tstruct __6123 noattr) ->
 eval_lvalue secp_ge e le m (odd_table_local_field name fid) b (Ptrofs.repr delta) Full.
Proof.
 intros Field Local.
 assert (Layout:In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]) by
  (destruct Field as [Same|[Same|[Same|Same]]];[left|right;left|right;right;left|contradiction];exact Same).
 destruct (gej_infinity_field_layout fid delta Layout) as (co & Lookup & Offset).
 unfold odd_table_local_field;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Evar_local;exact Local|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Lookup.
 - exact Offset.
Qed.
Lemma eval_odd_table_local_field_address e le m name fid delta b :
 In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> e!name=Some (b,Tstruct __6123 noattr) ->
 eval_expr secp_ge e le m (odd_table_local_field_address name fid) (Vptr b (Ptrofs.repr delta)).
Proof. intros Field Local;apply eval_Eaddrof;apply eval_odd_table_local_field;assumption. Qed.
Lemma eval_odd_table_first_entry e le m br : le!_pre_a=Some (Vptr br Ptrofs.zero) ->
 eval_expr secp_ge e le m odd_table_first_entry (Vptr br Ptrofs.zero).
Proof.
 intro Table;unfold odd_table_first_entry;eapply eval_Ebinop;
  [apply eval_Etempvar;exact Table|constructor|reflexivity].
Qed.

Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac keep_field H Frame := eapply field_at_lframe;[exact H|exact Frame|];intros;congruence.

Theorem exec_odd_table_head e le x y z m br bp bd bg :
 NoDup [br;bp;bd;bg] -> e!_d=Some (bd,Tstruct __6123 noattr) -> e!_d_ge=Some (bg,curve_ge_type) ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_ge_set_xy=None -> e!_secp256k1_ge_set_gej_zinv=None ->
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_pre_a=Some (Vptr br Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bd 0 128 Cur Freeable -> Mem.range_perm m bg 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m odd_table_head E0 le mf Out_normal /\
 fe_at mf br 0 (words5 (ge_zinv_x_words x (double_output_z_words y z))) /\
 fe_at mf br 40 (words5 (ge_zinv_y_words y (double_output_z_words y z))) /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
 Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
 fe_at mf bg 0 (words5 (double_output_x_words x y)) /\
 fe_at mf bg 40 (words5 (double_output_y_words x y)) /\ Mem.load Mint32 mf bg 80=Some (Vint Int.zero) /\
 fe_at mf bd 80 (words5 (double_output_z_words y z)) /\
 square_input_bounds (ge_zinv_x_words x (double_output_z_words y z)) /\
 square_input_bounds (ge_zinv_y_words y (double_output_z_words y z)) /\
 square_input_bounds (double_output_x_words x y) /\ square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
 Mem.range_perm mf bd 0 128 Cur Freeable /\ Mem.range_perm mf bg 0 88 Cur Freeable /\
 keeps_permissions m mf /\ lframe (odd_table_head_frame br bp bd bg) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct D DG DoubleGlobal XYGlobal ZinvGlobal A Table BX BY BZ X Y Z Flag FreeR FreeP FreeD FreeG.
 assert (Separate:br<>bp /\ br<>bd /\ br<>bg /\ bp<>bd /\ bp<>bg /\ bd<>bg).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Separate as (RP & RD & RG & PD & PG & DGsep).
 destruct (eval_double_var_separate_finite x y z m bd bp BX BY BZ ltac:(congruence) Flag X Y Z FreeD FreeP)
  as (m1 & Double & DX & DY & DZ & DFlag & PFlag & PX & PY & PZ & FreeD1 & FreeP1 & BDX & BDY & BDZ & FrameD & ReadonlyD).
 assert (KeepD:keeps_permissions m m1) by
  (eapply (secp_internal_keeps_permissions f_secp256k1_gej_double_var);[reflexivity|reflexivity|exact Double]).
 assert (FreeG1:Mem.range_perm m1 bg 0 88 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepD|exact FreeG]).
 destruct (eval_ge_set_xy_owned _ _ m1 bg bd ltac:(congruence) DX DY FreeG1)
  as (m2 & XY & GX & GY & GFlag & FreeG2 & PermXY & FrameXY).
 assert (KeepXY:keeps_permissions m1 m2) by (intros b pos k p P;apply (proj2 (PermXY b pos k p));exact P).
 assert (ReadonlyXY:readonly_preserved m1 m2) by
  (eapply (secp_closed_function_preserved f_secp256k1_ge_set_xy);[reflexivity|reflexivity|exact XY]).
 assert (PX2:fe_at m2 bp 0 (words5 x)) by (keep_field PX FrameXY).
 assert (PY2:fe_at m2 bp 40 (words5 y)) by (keep_field PY FrameXY).
 assert (PZ2:fe_at m2 bp 80 (words5 z)) by (keep_field PZ FrameXY).
 assert (DZ2:fe_at m2 bd 80 (words5 (double_output_z_words y z))) by (keep_field DZ FrameXY).
 assert (PFlag2:Mem.load Mint32 m2 bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameXY Mint32 bp 120);[exact PFlag| |intros;congruence].
   eapply Mem.perm_valid_block;apply (FreeP1 0);lia. }
 assert (Keep12:keeps_permissions m m2) by (eapply keeps_permissions_trans;[exact KeepD|exact KeepXY]).
 assert (FreeR2:Mem.range_perm m2 br 0 704 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep12|exact FreeR]).
 assert (FreeP2:Mem.range_perm m2 bp 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep12|exact FreeP]).
 assert (FreeD2:Mem.range_perm m2 bd 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep12|exact FreeD]).
 destruct (eval_ge_set_gej_zinv_indexed true 0 704 x y (double_output_z_words y z) m2 br bp bd Int.zero
   ltac:(lia) ltac:(exists 0;reflexivity) ltac:(lia)
   ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) RP RD PD BX BY BDZ PFlag2 PX2 PY2 DZ2
   FreeR2 FreeP2 FreeD2)
  as (mf & Zinv & RX & RY & RFlag & PFlagF & PXF & PYF & DZF & FreeRF & FreePF & FreeDF & BRX & BRY & FrameZ & ReadonlyZ).
 assert (KeepZ:keeps_permissions m2 mf) by
  (eapply (secp_internal_keeps_permissions f_secp256k1_ge_set_gej_zinv);[reflexivity|reflexivity|exact Zinv]).
 assert (PZF:fe_at mf bp 80 (words5 z)).
 { eapply curve_keep_field_range;[reflexivity|exact PZ2|exact FrameZ|];intros pos Range;
    unfold ge_zinv_indexed_frame;split;[exact PD|];split;[left;congruence|right;right;lia]. }
 assert (GXF:fe_at mf bg 0 (words5 (double_output_x_words x y))).
 { eapply field_at_lframe;[exact GX|exact FrameZ|];intros;unfold ge_zinv_indexed_frame;
    split;[congruence|];split;left;congruence. }
 assert (GYF:fe_at mf bg 40 (words5 (double_output_y_words x y))).
 { eapply field_at_lframe;[exact GY|exact FrameZ|];intros;unfold ge_zinv_indexed_frame;
    split;[congruence|];split;left;congruence. }
 assert (GFlagF:Mem.load Mint32 mf bg 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameZ Mint32 bg 80);[exact GFlag| |].
   - eapply Mem.perm_valid_block;apply (FreeG2 0);lia.
   - intros;unfold ge_zinv_indexed_frame;split;[congruence|];split;left;congruence. }
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact Keep12|exact KeepZ]).
 assert (FreeGF:Mem.range_perm mf bg 0 88 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep|exact FreeG]).
 assert (Frame:lframe (odd_table_head_frame br bp bd bg) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameD|];intros b pos (NR & NP & ND & NG) Valid;split;left;assumption.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameXY|];intros b pos (NR & NP & ND & NG) Valid;exact NG.
     + eapply lframe_implies;[exact FrameZ|];intros b pos (NR & NP & ND & NG) Valid;
        unfold ge_zinv_indexed_frame;split;[exact ND|];split;left;assumption. }
 assert (Readonly:readonly_preserved m mf) by
  (eapply preserved_trans;[exact ReadonlyD|];eapply preserved_trans;[exact ReadonlyXY|exact ReadonlyZ]).
 assert (DoubleRun:Clight2.exec_stmt secp_ge e le m
   (curve_call _secp256k1_gej_double_var f_secp256k1_gej_double_var None
    [odd_table_local_point _d;Etempvar _a (tptr (Tstruct __6123 noattr));
      Ecast (Econst_int Int.zero tint) (tptr tvoid)]) E0 le m1 Out_normal).
 { eapply exec_curve_call with (vargs:=[Vptr bd Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
   - original_pure.
   - exact DoubleGlobal.
   - eapply eval_Econs;[unfold odd_table_local_point;apply eval_Eaddrof;apply eval_Evar_local;exact D|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact A|reflexivity|].
     eapply eval_Econs;[eapply eval_Ecast;[constructor|reflexivity]|reflexivity|constructor].
   - exact Double. }
 assert (XYRun:Clight2.exec_stmt secp_ge e le m1
   (curve_call _secp256k1_ge_set_xy f_secp256k1_ge_set_xy None
    [Eaddrof (Evar _d_ge curve_ge_type) (tptr curve_ge_type);
      odd_table_local_field_address _d _x;odd_table_local_field_address _d _y]) E0 le m2 Out_normal).
 { eapply exec_curve_call with (vargs:=[Vptr bg Ptrofs.zero;Vptr bd Ptrofs.zero;Vptr bd (Ptrofs.repr 40)]) (v:=Vundef).
   - original_pure.
   - exact XYGlobal.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact DG|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_field_address with (b:=bd) (delta:=0);[left;reflexivity|exact D]|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_field_address with (b:=bd) (delta:=40);[right;left;reflexivity|exact D]|reflexivity|constructor].
   - exact XY. }
 assert (ZinvRun:Clight2.exec_stmt secp_ge e le m2
   (curve_call _secp256k1_ge_set_gej_zinv f_secp256k1_ge_set_gej_zinv None
    [odd_table_first_entry;Etempvar _a (tptr (Tstruct __6123 noattr));odd_table_local_field_address _d _z]) E0 le mf Out_normal).
 { eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bd (Ptrofs.repr 80)]) (v:=Vundef).
   - original_pure.
   - exact ZinvGlobal.
   - eapply eval_Econs;[apply eval_odd_table_first_entry;exact Table|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact A|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_field_address with (b:=bd) (delta:=80);[right;right;left;reflexivity|exact D]|reflexivity|constructor].
   - exact Zinv. }
 exists mf;split.
 - rewrite odd_table_head_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m) (out1:=Out_normal);
      [constructor|constructor|constructor|constructor].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact DoubleRun|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m2);[exact XYRun|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact ZinvRun|constructor].
 - repeat (first [assumption|split]).
Qed.

(** Establish the loop invariant with the original gej_set_ge call and two
    typed field copies. Unwritten table/ratio entries need no initial value. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_odd_table_head C.jet_secp_odd_table_loop C.jet_secp_curve_statements
 C.jet_secp_double_statements C.jet_secp_statement_prefix C.jet_secp_gej_set_ge_owned
 C.jet_secp_field_copy_owned C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_secp_curve_frame C.jet_secp_slice_permissions
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition odd_table_seed_statements := firstn 3 (skipn 4
 (fst (split_statement_last (fn_body f_secp256k1_ecmult_odd_multiples_table)))).
Definition odd_table_seed := statement_sequence odd_table_seed_statements (Sset _i (Econst_int Int.one tint)).
Definition odd_table_seed_fields := statement_sequence odd_table_seed_statements Sskip.
Definition odd_table_first_ratio := Ebinop Oadd (Etempvar _zr (tptr curve_fe_type))
 (Econst_int Int.zero tint) (tptr curve_fe_type).
Definition odd_table_seed_state x y z ratio :=
 {|odd_table_xs:=fun _=>x;odd_table_ys:=fun _=>y;odd_table_ratios:=fun _=>ratio;
   odd_table_x:=x;odd_table_y:=y;odd_table_z:=z;odd_table_flag:=Int.zero|}.
Definition odd_table_seed_frame (ba bz:block) (b:block) pos := b<>ba /\ (b<>bz \/ pos<0 \/ 40<=pos).

Lemma odd_table_seed_source : odd_table_seed=
 Ssequence (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
   [odd_table_local_point _ai;odd_table_first_entry])
 (Ssequence (Sassign (odd_table_local_field _ai _z) (double_point_field _a _z curve_fe_type))
 (Ssequence (Sassign (Ederef odd_table_first_ratio curve_fe_type) (odd_table_local_field _d _z))
 (Sset _i (Econst_int Int.one tint)))).
Proof. reflexivity. Qed.
Lemma eval_odd_table_input_field e le m bp fid delta :
 In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> le!_a=Some (Vptr bp Ptrofs.zero) ->
 eval_expr secp_ge e le m (double_point_field _a fid curve_fe_type) (Vptr bp (Ptrofs.repr delta)).
Proof.
 intros Field A;pose proof (eval_double_point_address e le m bp _a fid delta Field A) as Address.
 unfold double_point_address in Address;inversion Address;subst.
 - eapply eval_Elvalue;[eassumption|apply deref_loc_copy;reflexivity].
 - match goal with H:eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _=>inversion H end.
Qed.
Lemma eval_odd_table_first_ratio e le m bz : le!_zr=Some (Vptr bz Ptrofs.zero) ->
 eval_expr secp_ge e le m odd_table_first_ratio (Vptr bz Ptrofs.zero).
Proof.
 intro Ratios;unfold odd_table_first_ratio;eapply eval_Ebinop;
  [apply eval_Etempvar;exact Ratios|constructor|reflexivity].
Qed.

Theorem exec_odd_table_seed e le x y z ratio m ba br bp bd bz :
 NoDup [ba;br;bp;bd;bz] -> e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_d=Some (bd,Tstruct __6123 noattr) ->
 e!_secp256k1_gej_set_ge=None -> le!_pre_a=Some (Vptr br Ptrofs.zero) ->
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds ratio ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> Mem.load Mint32 m br 80=Some (Vint Int.zero) ->
 fe_at m bp 80 (words5 z) -> fe_at m bd 80 (words5 ratio) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m br 0 704 Cur Freeable ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bd 0 128 Cur Freeable ->
 Mem.range_perm m bz 0 320 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m odd_table_seed E0 (PTree.set _i (Vint Int.one) le) mf Out_normal /\
 Clight2.exec_stmt secp_ge e le m odd_table_seed_fields E0 le mf Out_normal /\
 odd_table_prefix mf br bz 1 (odd_table_seed_state x y z ratio) /\
 odd_table_prefix_bounds 1 (odd_table_seed_state x y z ratio) /\
 odd_table_accumulator mf ba (odd_table_seed_state x y z ratio) /\
 odd_table_accumulator_bounds (odd_table_seed_state x y z ratio) /\
 fe_at mf bp 80 (words5 z) /\ fe_at mf bd 80 (words5 ratio) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf br 0 704 Cur Freeable /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 128 Cur Freeable /\
 Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (odd_table_seed_frame ba bz) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct AI D Global Table A Ratios BX BY BZ BRatio X Y Flag Z R FreeA FreeT FreeP FreeD FreeR.
 assert (Separate:ba<>br /\ ba<>bp /\ ba<>bd /\ ba<>bz /\ br<>bz /\ bp<>bz /\ bd<>bz).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Separate as (AT & AP & AD & AR & TR & PR & DR).
 destruct (eval_gej_set_ge_owned m ba br x y Int.zero AT FreeA X Y Flag)
  as (m1 & SetCall & X1 & Y1 & One1 & Flag1 & FreeA1 & Frame1).
 assert (Keep1:keeps_permissions m m1) by
  (eapply (secp_internal_keeps_permissions f_secp256k1_gej_set_ge);[reflexivity|reflexivity|exact SetCall]).
 assert (Z1:fe_at m1 bp 80 (words5 z)) by
  (eapply field_at_lframe;[exact Z|exact Frame1|];intros;congruence).
 assert (R1:fe_at m1 bd 80 (words5 ratio)) by
  (eapply field_at_lframe;[exact R|exact Frame1|];intros;congruence).
 destruct (exec_field_copy_owned e le m1 (double_point_field _a _z curve_fe_type) (odd_table_local_field _ai _z)
   bp 80 ba 80 z eq_refl eq_refl
   ltac:(apply eval_odd_table_input_field;[right;right;left;reflexivity|exact A])
   ltac:(apply eval_odd_table_local_field;[right;right;left;reflexivity|exact AI])
   ltac:(congruence) Z1 ltac:(lia) ltac:(exists 10;reflexivity)
   ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia)
   ltac:(intros pos Range;apply FreeA1;lia))
  as (m2 & CopyZ & AZ2 & Perm2 & Frame2).
 assert (R2:fe_at m2 bd 80 (words5 ratio)) by
  (eapply field_at_lframe;[exact R1|exact Frame2|];intros;left;congruence).
 assert (Keep2:keeps_permissions m1 m2) by (intros b pos k p P;apply (proj2 (Perm2 b pos k p));exact P).
 assert (FreeR2:Mem.range_perm m2 bz 0 320 Cur Freeable) by
  (eapply keeps_range_permissions;[eapply keeps_permissions_trans;[exact Keep1|exact Keep2]|exact FreeR]).
 destruct (exec_field_copy_owned e le m2 (odd_table_local_field _d _z) (Ederef odd_table_first_ratio curve_fe_type)
   bd 80 bz 0 ratio eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_odd_table_local_field;[right;right;left;reflexivity|exact D]|apply deref_loc_copy;reflexivity])
   ltac:(apply eval_Ederef;apply eval_odd_table_first_ratio;exact Ratios)
   DR R2 ltac:(lia) ltac:(exists 0;reflexivity)
   ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia)
   ltac:(intros pos Range;apply FreeR2;lia))
  as (mf & CopyR & ROut & Perm3 & Frame3).
 assert (Keep:keeps_permissions m mf).
 { intros b pos k p P;apply (proj2 (Perm3 b pos k p)),(proj2 (Perm2 b pos k p)),Keep1;exact P. }
 assert (Frame:lframe (odd_table_seed_frame ba bz) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact Frame1|];intros b pos [NA NR] Valid;exact NA.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact Frame2|];intros b pos [NA NR] Valid;left;exact NA.
     + eapply lframe_implies;[exact Frame3|];intros b pos [NA NR] Valid;exact NR. }
 assert (AX2:fe_at m2 ba 0 (words5 x)) by
  (eapply curve_keep_field_range;[reflexivity|exact X1|exact Frame2|];intros pos Range;right;left;lia).
 assert (AY2:fe_at m2 ba 40 (words5 y)) by
  (eapply curve_keep_field_range;[reflexivity|exact Y1|exact Frame2|];intros pos Range;right;left;lia).
 assert (AFlag2:Mem.load Mint32 m2 ba 120=Some (Vint Int.zero)).
 { rewrite (proj1 Frame2 Mint32 ba 120);[exact Flag1| |].
   - eapply Mem.perm_valid_block;apply (FreeA1 0);lia.
   - intros pos Range;right;right;change (120<=pos<120+4) in Range;lia. }
 assert (AXF:fe_at mf ba 0 (words5 x)) by
  (eapply field_at_lframe;[exact AX2|exact Frame3|];intros;left;exact AR).
 assert (AYF:fe_at mf ba 40 (words5 y)) by
  (eapply field_at_lframe;[exact AY2|exact Frame3|];intros;left;exact AR).
 assert (AZF:fe_at mf ba 80 (words5 z)) by
  (eapply field_at_lframe;[exact AZ2|exact Frame3|];intros;left;exact AR).
 assert (AFlagF:Mem.load Mint32 mf ba 120=Some (Vint Int.zero)).
 { rewrite (proj1 Frame3 Mint32 ba 120);[exact AFlag2| |intros;left;exact AR].
   eapply Mem.perm_valid_block;apply (proj2 (Perm2 ba 0 Cur Freeable)),(FreeA1 0);lia. }
 assert (XF:fe_at mf br 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact Frame|];intros;split;[congruence|left;exact TR]).
 assert (YF:fe_at mf br 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y|exact Frame|];intros;split;[congruence|left;exact TR]).
 assert (FlagF:Mem.load Mint32 mf br 80=Some (Vint Int.zero)).
 { rewrite (proj1 Frame Mint32 br 80);[exact Flag| |intros;split;[congruence|left;exact TR]].
   eapply Mem.perm_valid_block;apply (FreeT 0);lia. }
 assert (ZF:fe_at mf bp 80 (words5 z)) by
  (eapply field_at_lframe;[exact Z|exact Frame|];intros;split;[congruence|left;exact PR]).
 assert (RF:fe_at mf bd 80 (words5 ratio)) by
  (eapply field_at_lframe;[exact R|exact Frame|];intros;split;[congruence|left;exact DR]).
 assert (Prefix:odd_table_prefix mf br bz 1 (odd_table_seed_state x y z ratio)).
 { intros j Bound;assert (J:j=0%nat) by lia;subst j;split;[exact XF|];split;[exact YF|];split;assumption. }
 assert (PrefixBounds:odd_table_prefix_bounds 1 (odd_table_seed_state x y z ratio)) by
  (intros j Bound;split;[exact BX|];split;assumption).
 assert (Acc:odd_table_accumulator mf ba (odd_table_seed_state x y z ratio)) by
  (split;[exact AXF|];split;[exact AYF|];split;assumption).
 assert (AccBounds:odd_table_accumulator_bounds (odd_table_seed_state x y z ratio)) by
  (split;[exact BX|];split;assumption).
 assert (FreeAF:Mem.range_perm mf ba 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeA]).
 assert (FreeTF:Mem.range_perm mf br 0 704 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeT]).
 assert (FreePF:Mem.range_perm mf bp 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeP]).
 assert (FreeDF:Mem.range_perm mf bd 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeD]).
 assert (FreeRF:Mem.range_perm mf bz 0 320 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep|exact FreeR]).
 assert (Readonly:readonly_preserved m mf).
 { eapply preserved_trans.
   - eapply (secp_closed_function_preserved f_secp256k1_gej_set_ge);[reflexivity|reflexivity|exact SetCall].
   - eapply preserved_trans;[inversion CopyZ;subst;eapply assign_preserved;eassumption|
      inversion CopyR;subst;eapply assign_preserved;eassumption]. }
 assert (SetRun:Clight2.exec_stmt secp_ge e le m
   (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None [odd_table_local_point _ai;odd_table_first_entry])
   E0 le m1 Out_normal).
 { eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero]) (v:=Vundef).
   - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   - exact Global.
   - eapply eval_Econs;[unfold odd_table_local_point;apply eval_Eaddrof;apply eval_Evar_local;exact AI|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_first_entry;exact Table|reflexivity|constructor].
   - exact SetCall. }
 assert (Fields:Clight2.exec_stmt secp_ge e le m odd_table_seed_fields E0 le mf Out_normal).
 { change (Clight2.exec_stmt secp_ge e le m
    (Ssequence (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None [odd_table_local_point _ai;odd_table_first_entry])
    (Ssequence (Sassign (odd_table_local_field _ai _z) (double_point_field _a _z curve_fe_type))
    (Ssequence (Sassign (Ederef odd_table_first_ratio curve_fe_type) (odd_table_local_field _d _z)) Sskip))) E0 le mf Out_normal).
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact SetRun|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m2);[exact CopyZ|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact CopyR|constructor]. }
 exists mf;split.
 - eapply exec_statement_prefix_then_last;[exact Fields|constructor;constructor].
 - repeat (first [assumption|split]).
Qed.

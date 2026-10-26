(** Whole original eight-entry odd-table function, including the three
    actual allocations and frees. Exact limb execution is established here;
    the connection to the canonical scalarTable5 program remains separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_odd_table_body C.jet_secp_odd_table_loop C.jet_secp_curve_statements
 C.jet_secp_double_coordinate_numeric C.jet_secp_double_all_calls C.jet_secp_square_columns
 C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_slice_permissions C.jet_secp_closed_helpers
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge odd_table_final_state point_mul_words.

Definition odd_table_env bd ba bg := PTree.set _d_ge (bg,curve_ge_type)
 (PTree.set _ai (ba,Tstruct __6123 noattr) (PTree.set _d (bd,Tstruct __6123 noattr) empty_env)).
Definition odd_table_entry_temps br bp bz bo := PTree.set _a (Vptr bp Ptrofs.zero)
 (PTree.set _z (Vptr bo Ptrofs.zero) (PTree.set _zr (Vptr bz Ptrofs.zero)
 (PTree.set _pre_a (Vptr br Ptrofs.zero) (PTree.set _n (Vint (Int.repr 8))
 (create_undef_temps (fn_temps f_secp256k1_ecmult_odd_multiples_table)))))).
Lemma odd_table_function_blocks bd ba bg : blocks_of_env secp_ge (odd_table_env bd ba bg)=
 [(ba,0,128);(bg,0,88);(bd,0,128)].
Proof. reflexivity. Qed.
Local Ltac allocated_valid := first [assumption |
 match goal with Alloc:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact Alloc end |
 match goal with Alloc:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact Alloc|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with Alloc:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite <-Eq;allocated_valid end |
 match goal with Alloc:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite Eq;allocated_valid end].

Theorem eval_ecmult_odd_table_eight x y z m br bp bz bo : NoDup [br;bp;bz;bo] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bz 0 320 Cur Freeable -> Mem.range_perm m bo 0 40 Cur Freeable ->
 let sf:=odd_table_final_state x y z in exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_odd_multiples_table)
  [Vint (Int.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef /\
 odd_table_prefix mf br bz 8 sf /\ odd_table_prefix_bounds 8 sf /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
 Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
 Mem.range_perm mf bz 0 320 Cur Freeable /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 keeps_permissions m mf /\ lframe (fun b _=>b<>br /\ b<>bp /\ b<>bz /\ b<>bo) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct BX BY BZ X Y Z Flag FreeT FreeP FreeR FreeO;cbv zeta.
 assert (VT:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FreeT 0);lia).
 assert (VP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (FreeP 0);lia).
 assert (VR:Mem.valid_block m bz) by (eapply Mem.perm_valid_block;apply (FreeR 0);lia).
 assert (VO:Mem.valid_block m bo) by (eapply Mem.perm_valid_block;apply (FreeO 0);lia).
 assert (Separate:br<>bp /\ br<>bz /\ br<>bo /\ bp<>bz /\ bp<>bo /\ bz<>bo).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Separate as (TP & TR & TO & PR & PO & RO).
 destruct (Mem.alloc m 0 128) as (m1 & bd) eqn:AllocD.
 destruct (Mem.alloc m1 0 128) as (m2 & ba) eqn:AllocA.
 destruct (Mem.alloc m2 0 88) as (mi & bg) eqn:AllocG.
 assert (Old:forall b,Mem.valid_block m b -> b<>bd /\ b<>ba /\ b<>bg) by
  (intros b Valid;repeat split;allocated_distinct).
 assert (DA:bd<>ba) by allocated_distinct.
 assert (DG:bd<>bg) by allocated_distinct.
 assert (AG:ba<>bg) by allocated_distinct.
 assert (SepAll:NoDup [br;bp;bz;bo;bd;ba;bg]).
 { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;repeat split;
    try apply NoDup_nil;try apply in_nil;first [congruence|allocated_distinct]. }
 assert (AllocFrame:lframe (fun _ _=>True) m mi).
 { eapply lframe_trans;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AllocD|].
   eapply lframe_trans;eapply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 assert (AllocKeep:keeps_permissions m mi).
 { eapply keeps_permissions_trans;[eapply alloc_keeps_permissions;exact AllocD|].
   eapply keeps_permissions_trans;eapply alloc_keeps_permissions;eassumption. }
 assert (XI:fe_at mi bp 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact AllocFrame|];intros;exact I).
 assert (YI:fe_at mi bp 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact AllocFrame|];intros;exact I).
 assert (ZI:fe_at mi bp 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact AllocFrame|];intros;exact I).
 assert (FlagI:Mem.load Mint32 mi bp 120=Some (Vint Int.zero)) by
  (rewrite (proj1 AllocFrame Mint32 bp 120 VP);[exact Flag|intros;exact I]).
 assert (FreeTI:Mem.range_perm mi br 0 704 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeT]).
 assert (FreePI:Mem.range_perm mi bp 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeP]).
 assert (FreeRI:Mem.range_perm mi bz 0 320 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeR]).
 assert (FreeOI:Mem.range_perm mi bo 0 40 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeO]).
 assert (FreeDI:Mem.range_perm mi bd 0 128 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AllocG|];eapply Mem.perm_alloc_1;[exact AllocA|];
    eapply Mem.perm_alloc_2;[exact AllocD|exact Range]. }
 assert (FreeAI:Mem.range_perm mi ba 0 128 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AllocG|];eapply Mem.perm_alloc_2;[exact AllocA|exact Range]. }
 assert (FreeGI:Mem.range_perm mi bg 0 88 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_alloc_2;[exact AllocG|exact Range]).
 set (e:=odd_table_env bd ba bg);set (le:=odd_table_entry_temps br bp bz bo).
 destruct (exec_odd_table_body e le x y z mi br bp bz bo bd ba bg SepAll
   eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
   eq_refl eq_refl eq_refl eq_refl eq_refl BX BY BZ XI YI ZI FlagI FreeTI FreePI FreeRI FreeOI FreeDI FreeAI FreeGI)
  as (lef & mo & Body & IF & Others & Prefix & PrefixBounds & Acc & AccBounds & Product & ProductBound & PX & PY & PZ & PFlag &
    FreeTO & FreePO & FreeRO & FreeOO & FreeDO & FreeAO & FreeGO & KeepBody & FrameBody & ReadonlyBody).
 destruct (free_list_exists [(ba,0,128);(bg,0,88);(bd,0,128)] mo) as (mf & Free & Unchanged).
 - repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Same|[Same|[Same|Same]]];try contradiction;inversion Same;subst;assumption.
 - assert (FrameFree:lframe (fun b _=>b<>bd /\ b<>ba /\ b<>bg) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|];intros b pos (ND & NA & NG) Valid;
      cbn;intuition congruence. }
   assert (PrefixF:odd_table_prefix mf br bz 8 (odd_table_final_state x y z)).
   { intros j Bound;destruct (Prefix j Bound) as (XJ & YJ & FlagJ & RJ);split.
     - eapply field_at_lframe;[exact XJ|exact FrameFree|];intros;exact (Old br VT).
     - split;[eapply field_at_lframe;[exact YJ|exact FrameFree|];intros;exact (Old br VT)|].
       split.
       + rewrite (proj1 FrameFree Mint32 br (88*Z.of_nat j+80));[exact FlagJ| |intros;exact (Old br VT)].
         eapply Mem.perm_valid_block;apply (FreeTO 0);lia.
       + eapply field_at_lframe;[exact RJ|exact FrameFree|];intros;exact (Old bz VR). }
   assert (ProductF:fe_at mf bo 0
     (words5 (point_mul_words (odd_table_z (odd_table_final_state x y z)) (double_output_z_words y z)))) by
    (eapply field_at_lframe;[exact Product|exact FrameFree|];intros;exact (Old bo VO)).
   assert (PXF:fe_at mf bp 0 (words5 x)) by (eapply field_at_lframe;[exact PX|exact FrameFree|];intros;exact (Old bp VP)).
   assert (PYF:fe_at mf bp 40 (words5 y)) by (eapply field_at_lframe;[exact PY|exact FrameFree|];intros;exact (Old bp VP)).
   assert (PZF:fe_at mf bp 80 (words5 z)) by (eapply field_at_lframe;[exact PZ|exact FrameFree|];intros;exact (Old bp VP)).
   assert (PFlagF:Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
   { rewrite (proj1 FrameFree Mint32 bp 120);[exact PFlag| |intros;exact (Old bp VP)].
     eapply Mem.perm_valid_block;apply (FreePO 0);lia. }
   assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_odd_multiples_table)
     [Vint (Int.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef).
   { eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mo) (out:=Out_normal).
     - assert (OK:fn_okb f_secp256k1_ecmult_odd_multiples_table=true) by reflexivity.
       destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
       constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
       eapply alloc_variables_cons with (m1:=m1) (b1:=bd);[exact AllocD|].
       eapply alloc_variables_cons with (m1:=m2) (b1:=ba);[exact AllocA|].
       eapply alloc_variables_cons with (m1:=mi) (b1:=bg);[exact AllocG|constructor].
     - exact Body.
     - reflexivity.
     - unfold e;rewrite odd_table_function_blocks;exact Free. }
   assert (Keep:keeps_permissions m mf) by
    (eapply (secp_internal_keeps_permissions f_secp256k1_ecmult_odd_multiples_table);[reflexivity|reflexivity|exact Call]).
   assert (Frame:lframe (fun b _=>b<>br /\ b<>bp /\ b<>bz /\ b<>bo) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>br /\ b<>bp /\ b<>bz /\ b<>bo).
     - eapply lframe_trans.
       + eapply lframe_implies;[exact AllocFrame|];intros;exact I.
       + eapply lframe_trans.
         * eapply lframe_implies;[exact FrameBody|];intros b pos (Valid & NT & NP & NR & NO) ValidI;
            destruct (Old b Valid) as (ND & NA & NG);unfold odd_table_body_frame;repeat split;assumption.
         * eapply lframe_implies;[exact FrameFree|];intros b pos (Valid & NT & NP & NR & NO) ValidO;exact (Old b Valid).
     - intros b pos Outside Valid;split;assumption. }
   exists mf;split;[exact Call|];split;[exact PrefixF|];split;[exact PrefixBounds|];
    split;[exact ProductF|];split;[exact ProductBound|];split;[exact PXF|];split;[exact PYF|];split;[exact PZF|];
    split;[exact PFlagF|];split;[eapply keeps_range_permissions;[exact Keep|exact FreeT]|];
    split;[eapply keeps_range_permissions;[exact Keep|exact FreeP]|];
    split;[eapply keeps_range_permissions;[exact Keep|exact FreeR]|];
    split;[eapply keeps_range_permissions;[exact Keep|exact FreeO]|];split;[exact Keep|];split;[exact Frame|].
   eapply (secp_closed_function_preserved f_secp256k1_ecmult_odd_multiples_table);[reflexivity|reflexivity|exact Call].
Qed.

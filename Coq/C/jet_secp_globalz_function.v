(** Whole original eight-entry global-Z function: actual local allocations,
    prefix, all seven iterations and both frees. The result is the exact
    checked limb traversal, not a public multiplication-jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_globalz_start C.jet_secp_globalz_loop C.jet_secp_globalz_iteration
 C.jet_secp_generator_globalz_empty C.jet_secp_field_weak_loose C.jet_secp_curve_statements
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_statement_prefix C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve C.jet_secp_closed_helpers.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge globalz_walk weak_loose_words.

Definition globalz_entry_temps br bz := PTree.set _zr (Vptr bz Ptrofs.zero)
 (PTree.set _a (Vptr br Ptrofs.zero) (PTree.set _len (Vlong (Int64.repr 8))
 (create_undef_temps (fn_temps f_secp256k1_ge_table_set_globalz)))).
Definition globalz_start_ys ys := globalz_replace ys 7 (weak_loose_words (ys 7%nat)).

Theorem eval_ge_table_set_globalz_eight xs ys ratios m br bz : br<>bz ->
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios ->
 globalz_table_rep m br xs ys -> globalz_ratios_rep m bz ratios ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 let '((xf,yf),_):=globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat) in exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_table_set_globalz)
  [Vlong (Int64.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero] E0 mf Vundef /\
 globalz_table_rep mf br xf yf /\ globalz_ratios_rep mf bz ratios /\ globalz_table_bounds xf yf /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (fun b _=>b<>br /\ b<>bz) m mf /\ readonly_preserved m mf.
Proof.
 intros Separate Bounds RatioBounds Table Ratios FreeA FreeR.
 destruct (Mem.alloc m 0 40) as [ma bf] eqn:AllocF.
 destruct (Mem.alloc ma 0 128) as [mb bt] eqn:AllocT.
 assert (Fresh:bf<>bt).
 { intro Same;apply (Mem.fresh_block_alloc _ _ _ _ _ AllocT);rewrite <-Same;
    eapply Mem.valid_new_block;exact AllocF. }
 assert (Old:forall b,Mem.valid_block m b -> b<>bf /\ b<>bt).
 { intros b Valid;split;intro Same;subst b.
   - exact (Mem.fresh_block_alloc _ _ _ _ _ AllocF Valid).
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AllocT);eapply Mem.valid_block_alloc;[exact AllocF|exact Valid]. }
 assert (ValidA:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FreeA 0);lia).
 assert (ValidR:Mem.valid_block m bz) by (eapply Mem.perm_valid_block;apply (FreeR 0);lia).
 destruct (Old br ValidA) as [AF AT];destruct (Old bz ValidR) as [RF RT].
 assert (Distinct:NoDup [br;bt;bf;bz]) by (repeat constructor;cbn;intuition congruence).
 assert (AllocFrame:lframe (fun _ _=>True) m mb).
 { eapply lframe_trans;eapply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 assert (AllocKeep:keeps_permissions m mb).
 { eapply keeps_permissions_trans;eapply alloc_keeps_permissions;eassumption. }
 assert (TableB:globalz_table_rep mb br xs ys).
 { intros j Bound;destruct (Table j Bound) as (X & Y & Flag);split.
   - eapply field_at_lframe;[exact X|exact AllocFrame|];intros;exact I.
   - split;[eapply field_at_lframe;[exact Y|exact AllocFrame|];intros;exact I|].
     rewrite (proj1 AllocFrame Mint32 br (88*Z.of_nat j+80) ValidA);[exact Flag|];intros;exact I. }
 assert (RatiosB:globalz_ratios_rep mb bz ratios).
 { intros j Bound;eapply field_at_lframe;[exact (Ratios j Bound)|exact AllocFrame|];intros;exact I. }
 assert (FreeAB:Mem.range_perm mb br 0 704 Cur Freeable) by
  (eapply keeps_range_permissions;[exact AllocKeep|exact FreeA]).
 assert (FreeRB:Mem.range_perm mb bz 0 320 Cur Freeable) by
  (eapply keeps_range_permissions;[exact AllocKeep|exact FreeR]).
 assert (FreeFB:Mem.range_perm mb bf 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AllocT|];eapply Mem.perm_alloc_2;[exact AllocF|exact Range]. }
 assert (FreeTB:Mem.range_perm mb bt 0 128 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_alloc_2;[exact AllocT|exact Range]).
 set (e:=globalz_empty_env bf bt).
 set (le:=globalz_entry_temps br bz).
 set (le1:=PTree.set _i (Vlong (Int64.repr 7)) le).
 assert (A:le1!_a=Some (Vptr br Ptrofs.zero)) by reflexivity.
 assert (ZR:le1!_zr=Some (Vptr bz Ptrofs.zero)) by reflexivity.
 assert (Length:le1!_len=Some (Vlong (Int64.repr 8))) by reflexivity.
 assert (Index:le1!_i=Some (Vlong (Int64.repr 7))) by reflexivity.
 destruct (exec_globalz_start e le1 mb br bf bz xs ys ratios AF Separate (not_eq_sym RF)
   eq_refl eq_refl A ZR Index Bounds RatioBounds TableB RatiosB FreeAB FreeFB FreeRB)
  as (ms & Start & TableS & RatiosS & ZS & BoundsS & FreeAS & FreeFS & FreeRS & KeepS & FrameS & ReadonlyS).
 assert (FreeTS:Mem.range_perm ms bt 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepS|exact FreeTB]).
 pose proof (exec_globalz_loop 7 ltac:(lia) e le1 ms br bt bf bz xs (globalz_start_ys ys) ratios
   (ratios 7%nat) Distinct eq_refl eq_refl eq_refl eq_refl A ZR Index Length
   BoundsS RatioBounds (RatioBounds 7%nat ltac:(lia)) TableS RatiosS ZS FreeAS FreeTS FreeFS FreeRS) as Loop.
 destruct (globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat)) as [[xf yf] zf] eqn:Walk.
 destruct Loop as (lef & ml & Run & FinalIndex & Temps & TableL & RatiosL & ZL & BoundsL & BZL
   & FreeAL & FreeTL & FreeFL & FreeRL & KeepL & FrameL & ReadonlyL).
 destruct (free_list_exists [(bt,0,128);(bf,0,40)] ml) as (mf & Free & Unchanged).
 - repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Same|[Same|Same]];try contradiction;inversion Same;subst;assumption.
 - assert (FrameF:lframe (fun b _=>b<>bf /\ b<>bt) ml mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos [NotF NotT] Valid;cbn;intuition congruence. }
   assert (TableF:globalz_table_rep mf br xf yf).
   { intros j Bound;destruct (TableL j Bound) as (X & Y & Flag);split.
     - eapply field_at_lframe;[exact X|exact FrameF|];intros;split;assumption.
     - split;[eapply field_at_lframe;[exact Y|exact FrameF|];intros;split;assumption|].
       assert (Valid:Mem.valid_block ml br) by (eapply Mem.perm_valid_block;apply (FreeAL 0);lia).
       rewrite (proj1 FrameF Mint32 br (88*Z.of_nat j+80) Valid);[exact Flag|];intros;split;assumption. }
   assert (RatiosF:globalz_ratios_rep mf bz ratios).
   { intros j Bound;eapply field_at_lframe;[exact (RatiosL j Bound)|exact FrameF|];intros;split;assumption. }
   assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_table_set_globalz)
     [Vlong (Int64.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero] E0 mf Vundef).
   { eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mb) (m2:=ml) (out:=Out_normal).
     - assert (OK:fn_okb f_secp256k1_ge_table_set_globalz=true) by reflexivity.
       destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
       constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
       eapply alloc_variables_cons with (m1:=ma) (b1:=bf);[exact AllocF|].
       eapply alloc_variables_cons with (m1:=mb) (b1:=bt);[exact AllocT|constructor].
     - rewrite globalz_empty_body_source.
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=mb).
       + apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;reflexivity|constructor|reflexivity].
       + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|].
         * eapply eval_Ebinop;[apply eval_Etempvar;exact Length|constructor|reflexivity].
         * rewrite <- (split_statement_last_exact globalz_nonempty_branch).
           eapply exec_statement_prefix_then_last;[exact Start|exact Run].
     - reflexivity.
     - unfold e;rewrite globalz_empty_blocks;exact Free. }
   assert (Keep:keeps_permissions m mf) by
    (eapply (secp_internal_keeps_permissions f_secp256k1_ge_table_set_globalz);[reflexivity|reflexivity|exact Call]).
   assert (Frame:lframe (fun b _=>b<>br /\ b<>bz) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>br /\ b<>bz).
     - eapply lframe_trans.
       + eapply lframe_implies;[exact AllocFrame|];intros;exact I.
       + eapply lframe_trans.
         * eapply lframe_implies;[exact FrameS|];intros b pos [Valid [NotA NotR]] ValidB;
            split;[exact (proj1 (Old b Valid))|left;exact NotA].
         * eapply lframe_trans.
           -- eapply lframe_implies;[exact FrameL|];intros b pos [Valid [NotA NotR]] ValidS;
               destruct (Old b Valid) as [NotF NotT];split;[exact NotA|];split;[exact NotT|];split;assumption.
           -- eapply lframe_implies;[exact FrameF|];intros b pos [Valid [NotA NotR]] ValidL;exact (Old b Valid).
     - intros b pos Outside Valid;split;assumption. }
   exists mf;split;[exact Call|];split;[exact TableF|];split;[exact RatiosF|];split;[exact BoundsL|];split.
   + eapply keeps_range_permissions;[exact Keep|exact FreeA].
   + split;[eapply keeps_range_permissions;[exact Keep|exact FreeR]|];split;[exact Keep|];split;[exact Frame|].
     eapply (secp_closed_function_preserved f_secp256k1_ge_table_set_globalz);[reflexivity|reflexivity|exact Call].
Qed.

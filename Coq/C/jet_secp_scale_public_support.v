(** The original public scale wrapper: four fresh locals, private frame copy,
    exact call spine, and all local frees. Execution premises here are
    discharged by the lifecycle theorem, not public proof assumptions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_clight_internal_preserve C.jet_secp_strauss_zero_generator C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding
 C.jet_secp_frame C.jet_secp_scale_startup C.jet_secp_strauss_complete_program.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition scale_public_env bl br ba bk :=
 PTree.set _na (bk,Tstruct __5826 noattr)
 (PTree.set _a (ba,Tstruct __6123 noattr)
 (PTree.set _r (br,Tstruct __6123 noattr)
 (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env))).
Definition scale_public_temps v_env bd base bs sbase :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
 (PTree.set _dst (Vptr bd (Ptrofs.repr base))
 (create_undef_temps (fn_temps f_simplicity_off_curve_scale)))).
Definition scale_public_storage (bl br ba bk:block) := [(bl,16);(br,128);(ba,128);(bk,32)].
Definition scale_public_locals (bl br ba bk:block) := [bl;br;ba;bk].
Lemma scale_public_entry_ok : fn_okb f_simplicity_off_curve_scale=true.
Proof. reflexivity. Qed.

Lemma scale_public_blocks bl br ba bk :
 blocks_of_env secp_ge (scale_public_env bl br ba bk)=
 [(bl,0,16);(ba,0,128);(br,0,128);(bk,0,32)].
Proof. reflexivity. Qed.
Local Ltac allocated_valid := first [assumption |
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact A end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with A:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite <-Eq;allocated_valid end |
 match goal with A:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite Eq;allocated_valid end].
Local Ltac allocated_perm Range := first [
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
  eapply Mem.perm_alloc_2;[exact A|exact Range] end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
  eapply Mem.perm_alloc_1;[exact A|allocated_perm Range] end].
Local Ltac allocated_frame := lazymatch goal with |- lframe _ ?ma ?mb =>
 tryif constr_eq ma mb then apply lframe_refl else
 match goal with A:Mem.alloc ma _ _=(?mi,_) |- _ =>
  eapply lframe_trans with (m2:=mi);
   [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A|allocated_frame] end end.

Theorem scale_public_entry v_env m bd base bs sbase : exists mi bl br ba bk,
 function_entry2 secp_ge f_simplicity_off_curve_scale
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (scale_public_env bl br ba bk) (scale_public_temps v_env bd base bs sbase) mi /\
 NoDup (scale_public_locals bl br ba bk) /\
 (forall b,Mem.valid_block m b ->~In b (scale_public_locals bl br ba bk)) /\
 (forall b hi,In (b,hi) (scale_public_storage bl br ba bk) ->
   Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 16) as (m1,bl) eqn:AL.
 destruct (Mem.alloc m1 0 128) as (m2,br) eqn:AK.
 destruct (Mem.alloc m2 0 128) as (m3,ba) eqn:AG.
 destruct (Mem.alloc m3 0 32) as (mi,bk) eqn:AP.
 assert (Entry:function_entry2 secp_ge f_simplicity_off_curve_scale
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (scale_public_env bl br ba bk) (scale_public_temps v_env bd base bs sbase) mi).
 { destruct (fn_okb_true _ scale_public_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bl);[exact AL|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=br);[exact AK|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=ba);[exact AG|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bk);[exact AP|constructor]. }
 assert (Distinct:NoDup (scale_public_locals bl br ba bk)).
 { unfold scale_public_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (scale_public_locals bl br ba bk)).
 { intros b Valid;unfold scale_public_locals;repeat rewrite not_in_cons;
   repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bl,br,ba,bk;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [scale_public_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|eapply entry_preserved;exact Entry].
Qed.


Lemma scale_public_free m bl br ba bk : NoDup (scale_public_locals bl br ba bk) ->
 (forall b hi,In (b,hi) (scale_public_storage bl br ba bk) ->
   Mem.range_perm m b 0 hi Cur Freeable) -> exists mf,
 Mem.free_list m (blocks_of_env secp_ge (scale_public_env bl br ba bk))=Some mf /\
 lframe (fun b _=>~In b (scale_public_locals bl br ba bk)) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct Free.
 destruct (free_list_exists [(bl,0,16);(ba,0,128);(br,0,128);(bk,0,32)] m)
   as (mf & Freed & Frame).
 - cbn;unfold scale_public_locals in Distinct;repeat rewrite NoDup_cons_iff in Distinct;
   cbn in Distinct;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_,_) = (_,_,_) |- _=>inversion S;subst b lo hi end;
   apply Free;clear;cbn [scale_public_storage In];tauto.
 - exists mf;split;[rewrite scale_public_blocks;exact Freed|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Frame|].
     intros b ofs Outside Valid;unfold scale_public_locals in Outside;cbn in *;intuition congruence.
   + eapply freelist_preserved;exact Freed.
Qed.


Require Import C.jet_sx_state C.jet_sx_expr C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout
 C.jet_frame_inv C.jet_secp_frame C.jet_secp_public_copy C.jet_secp_local_regions.
Definition scale_public_copy :=
 Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)).

Theorem scale_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc :
 scale_startup m0 -> write_frame_at m0 bd base bw edge cursor N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 exists mi md bl br ba bk,
 function_entry2 secp_ge f_simplicity_off_curve_scale
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m0
  (scale_public_env bl br ba bk) (scale_public_temps v_env bd base bs sbase) mi /\
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) (scale_public_temps v_env bd base bs sbase)
  mi scale_public_copy E0 (scale_public_temps v_env bd base bs sbase) md Out_normal /\
 (forall b hi,In (b,hi) (scale_public_storage bl br ba bk) -> Mem.range_perm md b 0 hi Cur Freeable) /\
 frame_fields_at md bl 0 bi inedge rc /\
 NoDup (scale_public_locals bl br ba bk) /\
 (forall b,Mem.valid_block m0 b -> ~In b (scale_public_locals bl br ba bk)) /\
 xsep (extA m0 bd bw bi) [(br,0);(ba,0);(bk,0);(bl,0)] /\
 finv m0 bd base bw edge cursor N bi md false [] /\ scale_startup md /\
 lframe (fun b _=>~In b (scale_public_locals bl br ba bk)) m0 md.
Proof.
 intros Ready Output Base Align Source.
 destruct (scale_public_entry v_env m0 bd base bs sbase)
  as (mi & bl & br & ba & bk & Entry & Separate & Old & Owned & AllocFrame & AllocRead).
 assert (SourceI:frame_fields_at mi bs sbase bi inedge rc).
 { destruct Source as [SE SC];pose proof (load_valid m0 Mptr bs sbase _ SE) as Valid;
   split;rewrite (proj1 AllocFrame) by auto;assumption. }
 destruct SourceI as [Edge Cursor].
 destruct (frame_loadbytes_at mi bs sbase _ _ Edge Cursor) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Length.
 assert (FreeL:Mem.range_perm mi bl 0 16 Cur Freeable).
 { apply Owned;clear;cbn [scale_public_storage In];tauto. }
 assert (Writable:Mem.range_perm mi bl 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Length;apply freeable_range_writable;exact FreeL. }
 destruct (Mem.range_perm_storebytes mi bl 0 bytes Writable) as (md & Store).
 assert (Frame:lframe (fun b _=>~In b (scale_public_locals bl br ba bk)) m0 md).
 { eapply lframe_trans;[eapply lframe_implies;[exact AllocFrame|intros;exact I]|].
   apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
   intros pos Range Outside;apply Outside;left;reflexivity. }
 assert (Ext:eqext m0 bd bw bi m0 md).
 { eapply lframe_implies;[exact Frame|].
   intros b pos [_ Valid] _;apply Old;exact Valid. }
 assert (Outside:bl<>bs).
 { intro Same;pose proof (Old bs (load_valid m0 Mptr bs sbase _ (proj1 Source))) as NotLocal.
   apply NotLocal;unfold scale_public_locals;left;exact Same. }
 assert (U:Ptrofs.unsigned (Ptrofs.repr sbase)=sbase) by
  (apply Ptrofs.unsigned_repr;unfold frame_base_valid in Base;lia).
 assert (Copy:Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk)
  (scale_public_temps v_env bd base bs sbase) mi scale_public_copy E0
  (scale_public_temps v_env bd base bs sbase) md Out_normal).
 { unfold scale_public_copy;eapply exec_Sassign_copy.
   - apply eval_Evar_local;reflexivity.
   - apply eval_Etempvar;unfold scale_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
   - reflexivity.
   - eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
     + reflexivity.
     + intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite U;exact Align.
     + intros _;change (8|0);exists 0;reflexivity.
     + left;congruence.
     + change (Mem.loadbytes mi bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes);rewrite U;exact Load.
     + exact Store. }
 exists mi,md,bl,br,ba,bk;split;[exact Entry|];split;[exact Copy|];split.
 - intros b hi Slot pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply (Owned b hi Slot);exact Range].
 - split;[exact (frame_copy_fields_at mi md bs sbase bl bytes _ _ Load Store Edge Cursor)|].
   split;[exact Separate|];split;[exact Old|];split.
   + intros r Index;assert (Local:In (blk [(br,0);(ba,0);(bk,0);(bl,0)] r)
     (scale_public_locals bl br ba bk)).
     { destruct r as [|[|[|[|r]]]];cbn [length] in Index;try lia;clear;
       cbn [blk bas lay nth fst scale_public_locals In];tauto. }
     unfold extA,fext;intros [_ Valid];exact (Old _ Valid Local).
   + split;[eapply finv_stable;[exact Output|apply finv_init;exact Output|exact Ext]|];split;[|exact Frame].
     eapply scale_startup_readonly;[exact Ready|].
     eapply preserved_trans;[exact AllocRead|eapply storebytes_preserved;exact Store].
Qed.

Require Import C.jet_clight_internal_frame C.jet_secp_scalar_add_body C.jet_secp_field_io_preserve C.jet_secp_frame_preserve
 C.jet_secp_curve_statements C.jet_secp_fns.
Definition scale_point_read := curve_call _read_gej f_read_gej None
 [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition scale_multiply := curve_call _secp256k1_ecmult f_secp256k1_ecmult None
 [Eaddrof (Evar _r (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _na (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar _ng (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition scale_write := curve_call _write_gej f_write_gej None
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));
  Eaddrof (Evar _r (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition scale_public_rest := Ssequence (scalar_add_read_stmt _na)
 (Ssequence scale_point_read (Ssequence scale_multiply
  (Ssequence scale_write (Sreturn (Some (Econst_int Int.one tint)))))).
Lemma scale_public_body_source :
 fn_body f_simplicity_off_curve_scale=Ssequence scale_public_copy scale_public_rest.
Proof. reflexivity. Qed.
Lemma scale_point_read_link :
 Genv.find_symbol secp_ge _read_gej=Some (secp_symbol_block _read_gej) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _read_gej) Ptrofs.zero)=Some (Internal f_read_gej).
Proof. split;reflexivity. Qed.
Lemma scale_write_link :
 Genv.find_symbol secp_ge _write_gej=Some (secp_symbol_block _write_gej) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _write_gej) Ptrofs.zero)=Some (Internal f_write_gej).
Proof. split;reflexivity. Qed.

Lemma scale_direct_void_call e le m mf id fd args vargs :
 Genv.find_symbol secp_ge id=Some (secp_symbol_block id) ->
 Genv.find_funct secp_ge (Vptr (secp_symbol_block id) Ptrofs.zero)=Some (Internal fd) ->
 e!id=None ->
 eval_exprlist secp_ge e le m args (type_of_params (fn_params fd)) vargs ->
 Clight2.eval_funcall secp_ge m (Internal fd) vargs E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (curve_call id fd None args) E0 le mf Out_normal.
Proof.
 intros Symbol Function Local Args Call;unfold curve_call.
 eapply exec_Scall with (vf:=Vptr (secp_symbol_block id) Ptrofs.zero)
  (f:=Internal fd) (vargs:=vargs) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Local|exact Symbol]|apply deref_loc_reference;reflexivity].
 - exact Args.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.

Lemma exec_scale_point_read le m mf bl br ba bk :
 Clight2.eval_funcall secp_ge m (Internal f_read_gej)
 [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le m scale_point_read E0 le mf Out_normal.
Proof.
 intro Call;unfold scale_point_read.
 eapply scale_direct_void_call;[exact (proj1 scale_point_read_link)|exact (proj2 scale_point_read_link)|reflexivity| |exact Call].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
Qed.

Lemma exec_scale_multiply le m mf bl br ba bk :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult)
 [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr strauss_zero_block Ptrofs.zero]
 E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le m scale_multiply E0 le mf Out_normal.
Proof.
 intro Call;unfold scale_multiply;eapply exec_curve_call with
 (vargs:=[Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr strauss_zero_block Ptrofs.zero])
 (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - reflexivity.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_strauss_zero_address;reflexivity|reflexivity|constructor].
 - exact Call.
Qed.

Lemma exec_scale_write le m mf bl br ba bk bd base :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_write_gej)
 [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le m scale_write E0 le mf Out_normal.
Proof.
 intros Dst Call;unfold scale_write.
 eapply scale_direct_void_call;[exact (proj1 scale_write_link)|exact (proj2 scale_write_link)|reflexivity| |exact Call].
 eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
Qed.

Theorem exec_scale_public_rest le m mr mp mn mw bl br ba bk bd base :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar) [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_secp256k1_ecmult)
 [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr strauss_zero_block Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_write_gej) [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mw Vundef ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le m scale_public_rest E0 le mw
 (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros Dst Scalar Point Mult Write;unfold scale_public_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mr).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Scalar].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mp);[eapply exec_scale_point_read;exact Point|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mn);[eapply exec_scale_multiply;exact Mult|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mw);
    [eapply exec_scale_write;[exact Dst|exact Write]|apply exec_Sreturn_some;constructor].
Qed.
Lemma scale_point_reader_closed : closed_stmtb field_io_helpers (fn_body f_read_gej)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma scale_point_reader_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal f_read_gej) args t mf result -> readonly_preserved m mf.
Proof.
 apply function_preserved_from_body;[|reflexivity].
 intros e le mi trace lef mo out Run Plain.
 exact (proj1 (internal_exec_preserved _ _ field_io_helpers_ok)
  e le mi _ trace lef mo out Run Plain scale_point_reader_closed).
Qed.

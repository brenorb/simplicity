From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Require Import C.jet_secp_checked_scale_startup C.jet_secp_scale_startup
 C.jet_secp_scale_public_support C.jet_secp_checked_scale_validity C.jet_sx_exec C.jet_sx_expr C.jet_sx_state
 C.jet_sx_rep C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout
 C.jet_frame_inv C.jet_secp_public_copy C.jet_secp_local_regions C.jet_secp_frame.
Definition checked_public_temps v_env bd base bs sbase :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
 (PTree.set _dst (Vptr bd (Ptrofs.repr base))
 (create_undef_temps (fn_temps f_simplicity_scale)))).

Lemma checked_public_entry_ok : fn_okb f_simplicity_scale=true. Proof. reflexivity. Qed.

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



Theorem checked_public_entry v_env m bd base bs sbase : exists mi bl br ba bk,
 function_entry2 secp_ge f_simplicity_scale
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (scale_public_env bl br ba bk) (checked_public_temps v_env bd base bs sbase) mi /\
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
 assert (Entry:function_entry2 secp_ge f_simplicity_scale
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (scale_public_env bl br ba bk) (checked_public_temps v_env bd base bs sbase) mi).
 { destruct (fn_okb_true _ checked_public_entry_ok) as (Vars & Params & Disjoint).
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

Theorem checked_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc :
 checked_scale_startup m0 -> write_frame_at m0 bd base bw edge cursor N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 exists mi md bl br ba bk,
 function_entry2 secp_ge f_simplicity_scale
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m0
  (scale_public_env bl br ba bk) (checked_public_temps v_env bd base bs sbase) mi /\
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) (checked_public_temps v_env bd base bs sbase)
  mi scale_public_copy E0 (checked_public_temps v_env bd base bs sbase) md Out_normal /\
 (forall b hi,In (b,hi) (scale_public_storage bl br ba bk) -> Mem.range_perm md b 0 hi Cur Freeable) /\
 frame_fields_at md bl 0 bi inedge rc /\
 NoDup (scale_public_locals bl br ba bk) /\
 (forall b,Mem.valid_block m0 b -> ~In b (scale_public_locals bl br ba bk)) /\
 xsep (extA m0 bd bw bi) [(br,0);(ba,0);(bk,0);(bl,0)] /\
 finv m0 bd base bw edge cursor N bi md false [] /\ checked_scale_startup md /\
 lframe (fun b _=>~In b (scale_public_locals bl br ba bk)) m0 md.
Proof.
 intros Ready Output Base Align Source.
 destruct (checked_public_entry v_env m0 bd base bs sbase)
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
  (checked_public_temps v_env bd base bs sbase) mi scale_public_copy E0
  (checked_public_temps v_env bd base bs sbase) md Out_normal).
 { unfold scale_public_copy;eapply exec_Sassign_copy.
   - apply eval_Evar_local;reflexivity.
   - apply eval_Etempvar;unfold checked_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
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
     eapply (scale_startup_readonly_at checked_zero_block);[exact Ready|].
     eapply preserved_trans;[exact AllocRead|eapply storebytes_preserved;exact Store].
Qed.


Require Import C.jet_secp_scalar_add_body C.jet_secp_curve_statements C.jet_clight_internal_frame.
Definition checked_scale_multiply := curve_call _secp256k1_ecmult f_secp256k1_ecmult None
 [Eaddrof (Evar _r (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _na (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar _ng__1 (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition checked_scale_branch := Sifthenelse (Etempvar _t'1 tbool)
 (Ssequence checked_scale_multiply
  (Ssequence scale_write (Sreturn (Some (Econst_int Int.one tint)))))
 (Sreturn (Some (Econst_int Int.zero tint))).
Definition checked_scale_rest := Ssequence (scalar_add_read_stmt _na)
 (Ssequence scale_point_read (Ssequence checked_curve_stmt checked_scale_branch)).
Lemma checked_scale_body_source : fn_body f_simplicity_scale=Ssequence scale_public_copy checked_scale_rest.
Proof. reflexivity. Qed.
Lemma checked_zero_symbol : Genv.find_symbol (genv_genv secp_ge) _ng__1=Some checked_zero_block.
Proof. vm_compute;reflexivity. Qed.
Lemma checked_mult_symbol : Genv.find_symbol secp_ge _secp256k1_ecmult=Some (secp_symbol_block _secp256k1_ecmult) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_ecmult) Ptrofs.zero)=Some (Internal f_secp256k1_ecmult).
Proof. split;reflexivity. Qed.
Lemma exec_checked_scale_multiply le m mf bl br ba bk :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult)
 [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr checked_zero_block Ptrofs.zero]
 E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le m checked_scale_multiply E0 le mf Out_normal.
Proof.
 intro Call;unfold checked_scale_multiply.
 eapply scale_direct_void_call;[exact (proj1 checked_mult_symbol)|exact (proj2 checked_mult_symbol)|reflexivity| |exact Call].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_global;[reflexivity|exact checked_zero_symbol]|reflexivity|constructor].
Qed.
Lemma exec_checked_scale_rest_true le md mr mp mv mn mw bd base bl br ba bk :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge md (Internal f_read_scalar)
  [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_simplicity_gej_is_valid_var)
  [Vptr ba Ptrofs.zero] E0 mv (Vint Int.one) ->
 Clight2.eval_funcall secp_ge mv (Internal f_secp256k1_ecmult)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr checked_zero_block Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_write_gej)
  [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mw Vundef ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le md checked_scale_rest E0
  (PTree.set _t'1 (Vint Int.one) le) mw (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros Dst Scalar Point Valid Mult Write;unfold checked_scale_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Scalar].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le);[eapply exec_scale_point_read;exact Point|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mv) (le1:=PTree.set _t'1 (Vint Int.one) le).
   + exact (exec_checked_curve le mp mv bl br ba bk true Valid).
   + unfold checked_scale_branch;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=PTree.set _t'1 (Vint Int.one) le);
        [eapply exec_checked_scale_multiply;exact Mult|].
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mw) (le1:=PTree.set _t'1 (Vint Int.one) le).
       -- eapply exec_scale_write;[rewrite PTree.gso by discriminate;exact Dst|exact Write].
       -- apply exec_Sreturn_some;constructor.
Qed.
Lemma exec_checked_scale_rest_false le md mr mp mv bl br ba bk :
 Clight2.eval_funcall secp_ge md (Internal f_read_scalar)
  [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_simplicity_gej_is_valid_var)
  [Vptr ba Ptrofs.zero] E0 mv (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge (scale_public_env bl br ba bk) le md checked_scale_rest E0
  (PTree.set _t'1 (Vint Int.zero) le) mv (Out_return (Some (Vint Int.zero,tint))).
Proof.
 intros Scalar Point Valid;unfold checked_scale_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Scalar].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le);[eapply exec_scale_point_read;exact Point|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mv) (le1:=PTree.set _t'1 (Vint Int.zero) le).
   + exact (exec_checked_curve le mp mv bl br ba bk false Valid).
   + unfold checked_scale_branch;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * apply exec_Sreturn_some;constructor.
Qed.

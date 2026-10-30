(** Entire original x-only serializer for a represented valid native key. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_sx_mem C.jet_sx_state C.jet_sx_rep C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_b32
 C.jet_secp_b32_exec C.jet_secp_b32_owned C.jet_secp_b32_full C.jet_read8s_layout C.jet_secp_curve_frame
 C.jet_secp_affine_storage C.jet_secp_table_decode C.jet_secp_storage_numeric C.jet_secp_pubkey_load_coordinates
 C.jet_secp_curve_literal C.jet_secp_xonly_tweak_entry C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_start
 C.jet_secp_schnorr_serialize_return C.jet_secp_statement_prefix C.jet_clight_nonnull_guard
 C.jet_memcpy_model C.jet_memset_model C.jet_secp_wnaf_memset
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve C.jet_sx_exec C.jet_word_repr.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition xonly_serialize_temps bout bin:=PTree.set _pubkey (Vptr bin Ptrofs.zero)
 (PTree.set _output32 (Vptr bout Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_xonly_pubkey_serialize))).
Definition xonly_serialize_clear:=Scall None
 (Evar _memset (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default))
 [Etempvar _output32 (tptr tuchar);Econst_int Int.zero tint;Econst_int (Int.repr 32) tint].
Definition xonly_serialize_start:=[nonnull_return_zero _output32 tuchar;xonly_serialize_clear;
 nonnull_return_zero _pubkey (Tstruct __6478 noattr)].
Definition xonly_serialize_load:=curve_call _secp256k1_xonly_pubkey_load f_secp256k1_xonly_pubkey_load (Some _t'1)
 [Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type);Etempvar _pubkey (tptr (Tstruct __6478 noattr))].
Definition xonly_serialize_write:=curve_call _secp256k1_fe_get_b32 f_secp256k1_fe_get_b32 None
 [Etempvar _output32 (tptr tuchar);schnorr_key_x_address].
Definition xonly_serialize_tail:=Ssequence (Ssequence xonly_serialize_load (xonly_parse_guard _t'1))
 (Ssequence xonly_serialize_write (Sreturn (Some (Econst_int Int.one tint)))).
Lemma xonly_serialize_body_source:fn_body f_secp256k1_xonly_pubkey_serialize=
 statement_sequence xonly_serialize_start xonly_serialize_tail.
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Theorem eval_xonly_pubkey_serialize (Copy:memcpy_model) (Clear:memset_model)
 (ax ay:Ty.tySem (Word 8)) w m bout bin:
 bout<>bin ->Mem.range_perm m bout 0 32 Cur Freeable ->Mem.range_perm m bin 0 64 Cur Freeable ->
 affine_storage_readable m bin 0 w ->field_storage_value w=@toZ (WordToZ 8) ax ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_serialize)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf (Vint Int.one) /\
 uint8_array_at mf bout 0 (map Int.repr (be_bytes (@toZ (WordToZ 8) ax))) /\
 Mem.range_perm mf bout 0 32 Cur Freeable /\Mem.range_perm mf bin 0 64 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Separate FO FI Input ValueX ValueY Curve.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (FO 0);lia).
 assert (VI:Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (FI 0);lia).
 destruct (Mem.alloc m 0 88) as (mi,bk) eqn:Alloc.
 pose (e:=xonly_tweak_env bk);pose (le:=xonly_serialize_temps bout bin).
 assert (Entry:function_entry2 secp_ge f_secp256k1_xonly_pubkey_serialize
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] m e le mi).
 { assert (OK:fn_okb f_secp256k1_xonly_pubkey_serialize=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons;[exact Alloc|constructor]. }
 assert (Fresh:forall b,Mem.valid_block m b ->b<>bk).
 { intros b Valid Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid). }
 assert (OK:bout<>bk) by (apply Fresh;exact VO).
 assert (IK:bin<>bk) by (apply Fresh;exact VI).
 assert (FrameI:lframe (fun _ _=>True) m mi) by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc).
 assert (KeepI:keeps_permissions m mi) by (eapply entry_keeps_permissions;exact Entry).
 assert (ReadI:readonly_preserved m mi) by (eapply entry_preserved;exact Entry).
 assert (FKI:Mem.range_perm mi bk 0 88 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range]).
 assert (FOI:Mem.range_perm mi bout 0 32 Cur Freeable) by (intros pos Range;apply KeepI,FO;exact Range).
 assert (VOI:Mem.valid_block mi bout) by (exact (proj1 (proj1 ReadI bout VO))).
 destruct (Clear secp_ge mi bout Ptrofs.zero Int.zero 32 VOI
  ltac:(rewrite Ptrofs.unsigned_zero;intros pos Range;eapply Mem.perm_implies;[apply FOI;exact Range|constructor])
  ltac:(clear;lia)) as (mz & Zero & Ext).
 rewrite Ptrofs.unsigned_zero in Zero.
 assert (KeepZ:keeps_permissions mi mz) by (intros b pos k p P;eapply Mem.perm_storebytes_1;[exact Zero|exact P]).
 assert (FrameZ:lframe (fun b _=>b<>bout) mi mz) by
  (apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Zero|intros;congruence]).
 assert (ReadZ:readonly_preserved mi mz) by (eapply storebytes_preserved;exact Zero).
 assert (ClearStmt:Clight2.exec_stmt secp_ge e le mi xonly_serialize_clear E0 le mz Out_normal).
 { destruct memset_linked as (bf & Sym & Funct);unfold xonly_serialize_clear;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
   (vargs:=[Vptr bout Ptrofs.zero;Vint Int.zero;Vlong (Int64.repr 32)])
   (f:=External (EF_external "memset" memset_sig)
    (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default) (vres:=Vptr bout Ptrofs.zero).
   - reflexivity.
   - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Sym]|apply deref_loc_reference;reflexivity].
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|constructor].
   - exact Funct.
   - reflexivity.
   - apply eval_funcall_external;exact Ext. }
 assert (Start:Clight2.exec_stmt secp_ge e le mi (statement_sequence xonly_serialize_start Sskip) E0 le mz Out_normal).
 { cbn [statement_sequence xonly_serialize_start];eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le).
   - apply exec_nonnull_return_zero with (b:=bout) (ofs:=Ptrofs.zero);[reflexivity|].
     apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
      [apply FOI;clear;change (0<=0<32);lia|apply perm_any_N].
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le);[exact ClearStmt|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le);[|constructor].
     apply exec_nonnull_return_zero with (b:=bin) (ofs:=Ptrofs.zero);[reflexivity|].
     apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
      [apply KeepZ,KeepI,FI;clear;change (0<=0<64);lia|apply perm_any_N]. }
 assert (InputZ:affine_storage_readable mz bin 0 w).
 { eapply affine_storage_readable_lframe;[|exact FrameZ|intros;clear -Separate;congruence].
   eapply affine_storage_readable_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (FKZ:Mem.range_perm mz bk 0 88 Cur Freeable) by (intros pos Range;apply KeepZ,FKI;exact Range).
 destruct (eval_xonly_pubkey_load_coordinates Copy w mz bin 0 bk ax ay FKZ InputZ ValueX ValueY Curve)
 as (ml & Load & X & Y & Flag & FKL & FrameL & ReadL).
 pose (lel:=PTree.set _t'1 (Vint Int.one) le).
 assert (LoadStmt:Clight2.exec_stmt secp_ge e le mz xonly_serialize_load E0 lel ml Out_normal).
 { unfold xonly_serialize_load;eapply exec_curve_call with (vargs:=[Vptr bk Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vint Int.one).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Load. }
 assert (FOL:Mem.range_perm ml bout 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia| |exact FrameL|intros;exact OK].
   intros pos Range;apply KeepZ,FOI;exact Range. }
 destruct (eval_fe_get_b32_owned ml bout 0 bk 0 (@toZ (WordToZ 8) ax) (word_toZ_range 8 ax)
  ltac:(clear;lia) ltac:(clear;change (32<=18446744073709551615);lia) FOL X OK)
 as (mb & Serialize & Bytes & XF & KeepB & FrameB & ReadB).
 assert (BlockFrame:lframe (fun b _=>b<>bout /\b<>bk) ml mb).
 { eapply lframe_implies;[exact FrameB|];intros b pos [NO NK] Valid Foot.
   destruct (get_b32_foot_bounds bout 0 bk 0 b pos Foot) as [[Same _]|[Same _]];congruence. }
 assert (WriteStmt:Clight2.exec_stmt secp_ge e lel ml xonly_serialize_write E0 lel mb Out_normal).
 { unfold xonly_serialize_write;eapply exec_curve_call with (vargs:=[Vptr bout Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_schnorr_key_x_address;reflexivity|reflexivity|constructor].
   - exact Serialize. }
 assert (FKB:Mem.range_perm mb bk 0 88 Cur Freeable) by (intros pos Range;apply KeepB,FKL;exact Range).
 destruct (xonly_tweak_free mb bk FKB) as (mf & Free & FrameF & ReadF).
 assert (Frame:lframe (fun b _=>b<>bout) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout).
   - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
     eapply lframe_trans;[eapply lframe_implies;[exact FrameZ|intros b pos [Old NO] Valid;exact NO]|].
     eapply lframe_trans;[eapply lframe_implies;[exact FrameL|intros b pos [Old NO] Valid;apply Fresh;exact Old]|].
     eapply lframe_trans;
      [eapply lframe_implies;[exact BlockFrame|intros b pos [Old NO] Valid;split;[exact NO|apply Fresh;exact Old]]|
       eapply lframe_implies;[exact FrameF|intros b pos [Old NO] Valid;apply Fresh;exact Old]].
   - intros b pos NO Old;split;assumption. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lel) (m1:=mi) (m2:=mb)
   (out:=Out_return (Some (Vint Int.one,tint))).
   + exact Entry.
   + rewrite xonly_serialize_body_source;eapply exec_statement_prefix_then_last;[exact Start|].
     unfold xonly_serialize_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ml) (le1:=lel).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact LoadStmt|apply exec_xonly_guard_one;apply PTree.gss].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact WriteStmt|apply exec_Sreturn_some;constructor].
   + split;[clear;discriminate|reflexivity].
   + exact Free.
 - split.
   + intros i v Nth;rewrite (proj1 FrameF Mint8unsigned bout (0+Z.of_nat i));[apply Bytes;exact Nth| |intros;exact OK].
     eapply Mem.perm_valid_block;apply (KeepB bout 0 Cur Freeable (FOL 0 ltac:(clear;lia))).
   + split.
     * eapply curve_keep_free;[clear;lia| |exact FrameF|intros;exact OK].
       intros pos Range;apply KeepB,FOL;exact Range.
     * split.
       -- eapply curve_keep_free;[clear;lia|exact FI|exact Frame|intros;clear -Separate;congruence].
       -- split;[exact Frame|].
          eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadZ|];
          eapply preserved_trans;[exact ReadL|];eapply preserved_trans;[exact ReadB|exact ReadF].
Qed.

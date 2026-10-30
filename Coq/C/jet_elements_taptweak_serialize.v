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
Require Import C.jet_secp_xonly_serialize C.jet_elements_taptweak_load_function
 C.jet_elements_taptweak_parser C.jet_elements_taptweak_pure C.jet_elements_taptweak_parse_start
 C.jet_transport C.jet_elements_taptweak_load_body.
Require Import C.jet_elements_taptweak_native_pure.
Definition elements_taptweak_serialize_helpers:=
 [(_secp256k1_xonly_pubkey_load,f_secp256k1_xonly_pubkey_load);
 (_secp256k1_fe_get_b32,f_secp256k1_fe_get_b32)].
Lemma elements_taptweak_serialize_lookup:
 map(secp_helper_lookup elements_taptweak_ge)elements_taptweak_serialize_helpers=
 map(fun it=>Some(Internal(snd it)))elements_taptweak_serialize_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_serialize_x_checked:
 expr_okb secp_ge elements_taptweak_ge schnorr_key_x_address=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.
Lemma eval_elements_taptweak_serialize_x e le m b:
 e!_pk=Some(b,curve_ge_type) ->eval_expr elements_taptweak_ge e le m schnorr_key_x_address(Vptr b Ptrofs.zero).
Proof.
 intro Key;apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m));
 [apply eval_schnorr_key_x_address;exact Key|exact elements_taptweak_serialize_x_checked].
Qed.
Lemma exec_elements_taptweak_serialize_call id fd result args vargs v e le m mf:
 In(id,fd)elements_taptweak_serialize_helpers ->e!id=None ->
 eval_exprlist elements_taptweak_ge e le m args(type_of_params(fn_params fd))vargs ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal fd)vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m(curve_call id fd result args)E0(set_opttemp result v le)mf Out_normal.
Proof.
 intros Member Global Args Call.
 destruct(secp_helper_lookup_exists elements_taptweak_ge id fd
 (secp_map_eq_in _ _ _ elements_taptweak_serialize_lookup (id,fd) Member))as(bf & Sym & Funct).
 eapply exec_elements_taptweak_curve_call with(bf:=bf);[exact Sym| |exact Global|exact Args|exact Call].
 unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
Qed.
Theorem eval_elements_taptweak_xonly_serialize (Copy:memcpy_model) (Clear:memset_model)
 (ax ay:Ty.tySem (Word 8)) w m bout bin:
 bout<>bin ->Mem.range_perm m bout 0 32 Cur Freeable ->Mem.range_perm m bin 0 64 Cur Freeable ->
 affine_storage_readable m bin 0 w ->field_storage_value w=@toZ (WordToZ 8) ax ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_serialize)
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
 assert (Entry:function_entry2 elements_taptweak_ge f_secp256k1_xonly_pubkey_serialize
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] m e le mi).
 { assert (OK:fn_okb f_secp256k1_xonly_pubkey_serialize=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with(m1:=mi)(b1:=bk).
   - change(Mem.alloc m 0(sizeof elements_taptweak_ge curve_ge_type)=(mi,bk)).
     rewrite(proj2 elements_taptweak_parser_sizes);exact Alloc.
   - constructor. }
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
 destruct (Clear elements_taptweak_ge mi bout Ptrofs.zero Int.zero 32 VOI
  ltac:(rewrite Ptrofs.unsigned_zero;intros pos Range;eapply Mem.perm_implies;[apply FOI;exact Range|constructor])
  ltac:(clear;lia)) as (mz & Zero & Ext).
 rewrite Ptrofs.unsigned_zero in Zero.
 assert (KeepZ:keeps_permissions mi mz) by (intros b pos k p P;eapply Mem.perm_storebytes_1;[exact Zero|exact P]).
 assert (FrameZ:lframe (fun b _=>b<>bout) mi mz) by
  (apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Zero|intros;congruence]).
 assert (ReadZ:readonly_preserved mi mz) by (eapply storebytes_preserved;exact Zero).
 assert (ClearStmt:Clight2.exec_stmt elements_taptweak_ge e le mi xonly_serialize_clear E0 le mz Out_normal).
 { destruct elements_taptweak_memset_linked as (bf & Sym & Funct);unfold xonly_serialize_clear;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
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
 assert (Start:Clight2.exec_stmt elements_taptweak_ge e le mi (statement_sequence xonly_serialize_start Sskip) E0 le mz Out_normal).
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
 destruct (eval_elements_taptweak_xonly_pubkey_load_coordinates Copy w mz bin 0 bk ax ay FKZ InputZ ValueX ValueY Curve)
 as (ml & Load & X & Y & Flag & FKL & FrameL & ReadL).
 pose (lel:=PTree.set _t'1 (Vint Int.one) le).
 assert (LoadStmt:Clight2.exec_stmt elements_taptweak_ge e le mz xonly_serialize_load E0 lel ml Out_normal).
 { unfold xonly_serialize_load;eapply exec_elements_taptweak_serialize_call with (vargs:=[Vptr bk Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vint Int.one).
   - unfold elements_taptweak_serialize_helpers;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Load. }
 assert (FOL:Mem.range_perm ml bout 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia| |exact FrameL|intros;exact OK].
   intros pos Range;apply KeepZ,FOI;exact Range. }
 destruct (eval_elements_taptweak_fe_get_b32_owned ml bout 0 bk 0 (@toZ (WordToZ 8) ax) (word_toZ_range 8 ax)
  ltac:(clear;lia) ltac:(clear;change (32<=18446744073709551615);lia) FOL X OK)
 as (mb & Serialize & Bytes & XF & KeepB & FrameB & ReadB).
 assert (BlockFrame:lframe (fun b _=>b<>bout /\b<>bk) ml mb).
 { eapply lframe_implies;[exact FrameB|];intros b pos [NO NK] Valid Foot.
   destruct (get_b32_foot_bounds bout 0 bk 0 b pos Foot) as [[Same _]|[Same _]];congruence. }
 assert (WriteStmt:Clight2.exec_stmt elements_taptweak_ge e lel ml xonly_serialize_write E0 lel mb Out_normal).
 { unfold xonly_serialize_write;eapply exec_elements_taptweak_serialize_call with (vargs:=[Vptr bout Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
   - unfold elements_taptweak_serialize_helpers;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_elements_taptweak_serialize_x;reflexivity|reflexivity|constructor].
   - exact Serialize. }
 assert (FKB:Mem.range_perm mb bk 0 88 Cur Freeable) by (intros pos Range;apply KeepB,FKL;exact Range).
 destruct (elements_taptweak_single_point_free mb bk FKB) as (mf & Free & FrameF & ReadF).
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
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact LoadStmt|apply exec_elements_taptweak_xonly_guard_one;apply PTree.gss].
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

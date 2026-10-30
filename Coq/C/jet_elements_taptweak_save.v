(** Complete original native-storage public-key save function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_memcpy_model C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_field_read_preservation
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_affine_storage C.jet_secp_table_decode C.jet_secp_pubkey_copy C.jet_secp_pubkey_load_body
 C.jet_secp_storage_numeric C.jet_secp_fe_inv_prefix C.jet_secp_ge_storage_body C.jet_secp_ge_storage_function
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require Import C.jet_secp_pubkey_save_copy.
Require Import C.jet_secp_pubkey_save_function C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_parse_start
 C.jet_xonly_parse_control_at C.jet_transport.
Require Import C.jet_elements_taptweak_save_copy.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_curve_has_storage:
 In (_secp256k1_ge_to_storage,f_secp256k1_ge_to_storage) elements_taptweak_curve_helpers.
Proof.
 assert (Found:find (fun it=>Pos.eqb (fst it) _secp256k1_ge_to_storage)
 elements_taptweak_curve_helpers=Some (_secp256k1_ge_to_storage,f_secp256k1_ge_to_storage))
 by (vm_compute;reflexivity).
 apply find_some in Found;exact (proj1 Found).
Qed.
Lemma elements_taptweak_storage_test_checked:
 expr_okb secp_ge elements_taptweak_ge pubkey_load_size_test=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_pubkey_save_lookup:
 secp_helper_lookup elements_taptweak_ge (_secp256k1_pubkey_save,f_secp256k1_pubkey_save)=
 Some (Internal f_secp256k1_pubkey_save).
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.
Theorem eval_elements_taptweak_ge_to_storage_owned wx wy m bin bout:
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ge_to_storage)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 field_storage_value (ge_storage_words wx wy)=fe_inv_value wx /\
 field_storage_value (fun i=>ge_storage_words wx wy (4+i)%nat)=fe_inv_value wy /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros BX BY X Y Free;destruct (eval_ge_to_storage_owned wx wy m bin bout BX BY X Y Free)
 as (mf & Call & Memory);exists mf;split;[|exact Memory].
 exact (elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_curve_has_storage Call).
Qed.
Lemma elements_taptweak_pubkey_save_blocks bs:blocks_of_env elements_taptweak_ge (pubkey_save_env bs)=[(bs,0,64)].
Proof.
 change ([(bs,0,sizeof (genv_cenv elements_taptweak_ge) pubkey_storage_type)]=[(bs,0,64)]).
 rewrite elements_taptweak_pubkey_storage_size;reflexivity.
Qed.
Theorem elements_taptweak_pubkey_save_entry_owned m key point:
 exists mi bs,
 function_entry2 elements_taptweak_ge f_secp256k1_pubkey_save [key;point] m
 (pubkey_save_env bs) (pubkey_save_temps key point) mi /\
 (forall b,Mem.valid_block m b ->b<>bs) /\Mem.range_perm mi bs 0 64 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 64) as (mi,bs) eqn:Alloc.
 assert (Entry:function_entry2 elements_taptweak_ge f_secp256k1_pubkey_save [key;point] m
 (pubkey_save_env bs) (pubkey_save_temps key point) mi).
 { assert (OK:fn_okb f_secp256k1_pubkey_save=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bs).
   - change (Mem.alloc m 0 (sizeof (genv_cenv elements_taptweak_ge) pubkey_storage_type)=(mi,bs)).
     rewrite elements_taptweak_pubkey_storage_size;exact Alloc.
   - constructor. }
 exists mi,bs;split;[exact Entry|];split.
 - intros b Valid Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
 - split;[intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range]|];split.
   + apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc.
   + split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
Theorem elements_taptweak_eval_pubkey_save (Model:memcpy_model) wx wy m bin bout:
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_pubkey_save)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros BoundsX BoundsY InputX InputY Free.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 destruct (elements_taptweak_pubkey_save_entry_owned m (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
 as (mi & bs & Entry & Fresh & FreeS & FrameI & KeepI & ReadI).
 assert (OutFresh:bout<>bs) by (apply Fresh;exact VO).
 assert (InputsI:fe_at mi bin 0 (words5 wx) /\fe_at mi bin 40 (words5 wy)).
 { split;eapply field_at_lframe;[exact InputX|exact FrameI|intros;exact I|
  exact InputY|exact FrameI|intros;exact I]. }
 destruct InputsI as [XI YI].
 destruct (eval_elements_taptweak_ge_to_storage_owned wx wy mi bin bs BoundsX BoundsY XI YI FreeS)
 as (mp & Pack & Storage & ValueX & ValueY & FreeSP & FrameP & ReadP).
 assert (FreeOutP:Mem.range_perm mp bout 0 64 Cur Freeable).
 { eapply curve_keep_free;[lia| |exact FrameP|intros;exact OutFresh].
   intros pos Range;apply KeepI,Free;exact Range. }
 pose (e:=pubkey_save_env bs).
 pose (le:=pubkey_save_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero)).
 destruct (exec_elements_taptweak_pubkey_save_copy Model (ge_storage_words wx wy) e le mp bs bout
  eq_refl eq_refl eq_refl OutFresh FreeOutP Storage)
 as (mb & Copy & Output & FreeOutB & FrameC & ReadC).
 assert (PackStmt:Clight2.exec_stmt elements_taptweak_ge e le mi pubkey_save_pack E0 le mp Out_normal).
 { unfold pubkey_save_pack;destruct (elements_taptweak_curve_entries _ _ elements_taptweak_curve_has_storage) as (b1 & b2 & S1 & F1 & S2 & F2).
   eapply exec_elements_taptweak_curve_call with (bf:=b2) (vargs:=[Vptr bs Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vundef).
   - exact S2.
   - unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact F2.
   - reflexivity.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Pack. }
 assert (Body:Clight2.exec_stmt elements_taptweak_ge e le mi (fn_body f_secp256k1_pubkey_save) E0 le mb Out_normal).
 { rewrite pubkey_save_body_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   - apply (proj1 (eval_expr_transport secp_ge elements_taptweak_ge e le mi)).
     + unfold pubkey_load_size_test;eapply eval_Ebinop;[apply eval_Esizeof|constructor|reflexivity].
     + exact elements_taptweak_storage_test_checked.
   - reflexivity.
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le);[exact PackStmt|exact Copy]. }
 assert (FreeSB:Mem.range_perm mb bs 0 64 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FreeSP|exact FrameC|intros;congruence]. }
 destruct (Mem.range_perm_free mb bs 0 64 FreeSB) as (mf & Frees).
 assert (FrameF:lframe (fun b _=>b<>bs) mb mf).
 { apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Frees|intros;congruence]. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=le) (m1:=mi) (m2:=mb) (out:=Out_normal).
   + exact Entry.
   + exact Body.
   + reflexivity.
   + change (Mem.free_list mb (blocks_of_env elements_taptweak_ge (pubkey_save_env bs))=Some mf).
     rewrite elements_taptweak_pubkey_save_blocks;cbn [Mem.free_list];rewrite Frees;reflexivity.
 - split.
   + eapply affine_storage_readable_lframe;[exact Output|exact FrameF|intros;exact OutFresh].
   + split.
     * eapply curve_keep_free;[lia|exact FreeOutB|exact FrameF|intros;exact OutFresh].
     * split.
       { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout).
         - eapply lframe_trans.
           + eapply lframe_implies;[exact FrameI|intros;exact I].
           + eapply lframe_trans.
             * eapply lframe_implies;[exact FrameP|];intros b pos [Valid _] _;apply Fresh;exact Valid.
             * eapply lframe_trans.
               -- eapply lframe_implies;[exact FrameC|];intros b pos [_ Other] _;exact Other.
               -- eapply lframe_implies;[exact FrameF|];intros b pos [Valid _] _;apply Fresh;exact Valid.
         - intros b pos Other Valid;split;assumption. }
       { eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadP|].
         eapply preserved_trans;[exact ReadC|];eapply free_preserved;exact Frees. }
Qed.
Definition xonly_save_temps key point:=PTree.set _ge point (PTree.set _pubkey key (PTree.empty val)).
Lemma elements_taptweak_xonly_pubkey_save_entry m key point:
 function_entry2 elements_taptweak_ge f_secp256k1_xonly_pubkey_save [key;point] m empty_env
 (xonly_save_temps key point) m.
Proof.
 assert (OK:fn_okb f_secp256k1_xonly_pubkey_save=true) by reflexivity.
 destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
Qed.
Theorem elements_taptweak_eval_xonly_pubkey_save (Model:memcpy_model) wx wy m bin bout:
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_save)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros BoundsX BoundsY InputX InputY Free.
 destruct (elements_taptweak_eval_pubkey_save Model wx wy m bin bout BoundsX BoundsY InputX InputY Free)
 as (mf & Save & Storage & FreeF & Frame & Read).
 pose (le:=xonly_save_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero)).
 assert (Body:Clight2.exec_stmt elements_taptweak_ge empty_env le m
  (curve_call _secp256k1_pubkey_save f_secp256k1_pubkey_save None
   [Ecast (Etempvar _pubkey (tptr (Tstruct __6478 noattr))) (tptr pubkey_opaque_type);
    Etempvar _ge (tptr curve_ge_type)]) E0 le mf Out_normal).
 { destruct (secp_helper_lookup_exists elements_taptweak_ge _ _ elements_taptweak_pubkey_save_lookup) as (bf & Sym & Funct).
   eapply exec_elements_taptweak_curve_call with (bf:=bf) (vargs:=[Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vundef).
   - exact Sym.
   - unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
   - reflexivity.
   - eapply eval_Econs;[eapply eval_Ecast;[apply eval_Etempvar;reflexivity|reflexivity]|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Save. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply elements_taptweak_xonly_pubkey_save_entry.
   + exact Body.
   + reflexivity.
   + reflexivity.
 - split;[exact Storage|];split;[exact FreeF|];split;assumption.
Qed.

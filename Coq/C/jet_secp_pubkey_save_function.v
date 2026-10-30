(** Complete original native-storage public-key save function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_memcpy_model C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_field_read_preservation
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_affine_storage C.jet_secp_table_decode C.jet_secp_pubkey_copy C.jet_secp_pubkey_load_body
 C.jet_secp_storage_numeric C.jet_secp_fe_inv_prefix C.jet_secp_ge_storage_body C.jet_secp_ge_storage_function
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require Import C.jet_secp_pubkey_save_copy.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition pubkey_save_env bs:=PTree.set _s (bs,pubkey_storage_type) empty_env.
Definition pubkey_save_temps key point:=PTree.set _ge point (PTree.set _pubkey key
 (create_undef_temps (fn_temps f_secp256k1_pubkey_save))).
Definition pubkey_save_pack:=curve_call _secp256k1_ge_to_storage f_secp256k1_ge_to_storage None
 [Eaddrof (Evar _s pubkey_storage_type) (tptr pubkey_storage_type);Etempvar _ge (tptr curve_ge_type)].
Definition pubkey_save_other:=match fn_body f_secp256k1_pubkey_save with
 |Sifthenelse _ _ other=>other|_=>Sskip end.
Lemma pubkey_save_body_source:fn_body f_secp256k1_pubkey_save=
 Sifthenelse pubkey_load_size_test (Ssequence pubkey_save_pack pubkey_save_copy_stmt) pubkey_save_other.
Proof. reflexivity. Qed.
Lemma pubkey_save_blocks bs:blocks_of_env secp_ge (pubkey_save_env bs)=[(bs,0,64)].
Proof. reflexivity. Qed.
Theorem pubkey_save_entry_owned m key point:
 exists mi bs,
 function_entry2 secp_ge f_secp256k1_pubkey_save [key;point] m
 (pubkey_save_env bs) (pubkey_save_temps key point) mi /\
 (forall b,Mem.valid_block m b ->b<>bs) /\Mem.range_perm mi bs 0 64 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 64) as (mi,bs) eqn:Alloc.
 assert (Entry:function_entry2 secp_ge f_secp256k1_pubkey_save [key;point] m
 (pubkey_save_env bs) (pubkey_save_temps key point) mi).
 { assert (OK:fn_okb f_secp256k1_pubkey_save=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons;[exact Alloc|constructor]. }
 exists mi,bs;split;[exact Entry|];split.
 - intros b Valid Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
 - split;[intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range]|];split.
   + apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc.
   + split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
Theorem eval_pubkey_save (Model:memcpy_model) wx wy m bin bout:
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_pubkey_save)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros BoundsX BoundsY InputX InputY Free.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 destruct (pubkey_save_entry_owned m (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
 as (mi & bs & Entry & Fresh & FreeS & FrameI & KeepI & ReadI).
 assert (OutFresh:bout<>bs) by (apply Fresh;exact VO).
 assert (InputsI:fe_at mi bin 0 (words5 wx) /\fe_at mi bin 40 (words5 wy)).
 { split;eapply field_at_lframe;[exact InputX|exact FrameI|intros;exact I|
  exact InputY|exact FrameI|intros;exact I]. }
 destruct InputsI as [XI YI].
 destruct (eval_ge_to_storage_owned wx wy mi bin bs BoundsX BoundsY XI YI FreeS)
 as (mp & Pack & Storage & ValueX & ValueY & FreeSP & FrameP & ReadP).
 assert (FreeOutP:Mem.range_perm mp bout 0 64 Cur Freeable).
 { eapply curve_keep_free;[lia| |exact FrameP|intros;exact OutFresh].
   intros pos Range;apply KeepI,Free;exact Range. }
 pose (e:=pubkey_save_env bs).
 pose (le:=pubkey_save_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero)).
 destruct (exec_pubkey_save_copy Model (ge_storage_words wx wy) e le mp bs bout
  eq_refl eq_refl eq_refl OutFresh FreeOutP Storage)
 as (mb & Copy & Output & FreeOutB & FrameC & ReadC).
 assert (PackStmt:Clight2.exec_stmt secp_ge e le mi pubkey_save_pack E0 le mp Out_normal).
 { unfold pubkey_save_pack;eapply exec_curve_call with (vargs:=[Vptr bs Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Pack. }
 assert (Body:Clight2.exec_stmt secp_ge e le mi (fn_body f_secp256k1_pubkey_save) E0 le mb Out_normal).
 { rewrite pubkey_save_body_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   - unfold pubkey_load_size_test;eapply eval_Ebinop;[apply eval_Esizeof|constructor|reflexivity].
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
   + change (Mem.free_list mb (blocks_of_env secp_ge (pubkey_save_env bs))=Some mf).
     rewrite pubkey_save_blocks;cbn [Mem.free_list];rewrite Frees;reflexivity.
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
Lemma xonly_pubkey_save_entry m key point:
 function_entry2 secp_ge f_secp256k1_xonly_pubkey_save [key;point] m empty_env
 (xonly_save_temps key point) m.
Proof.
 assert (OK:fn_okb f_secp256k1_xonly_pubkey_save=true) by reflexivity.
 destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
Qed.
Theorem eval_xonly_pubkey_save (Model:memcpy_model) wx wy m bin bout:
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_save)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros BoundsX BoundsY InputX InputY Free.
 destruct (eval_pubkey_save Model wx wy m bin bout BoundsX BoundsY InputX InputY Free)
 as (mf & Save & Storage & FreeF & Frame & Read).
 pose (le:=xonly_save_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero)).
 assert (Body:Clight2.exec_stmt secp_ge empty_env le m
  (curve_call _secp256k1_pubkey_save f_secp256k1_pubkey_save None
   [Ecast (Etempvar _pubkey (tptr (Tstruct __6478 noattr))) (tptr pubkey_opaque_type);
    Etempvar _ge (tptr curve_ge_type)]) E0 le mf Out_normal).
 { eapply exec_curve_call with (vargs:=[Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[eapply eval_Ecast;[apply eval_Etempvar;reflexivity|reflexivity]|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Save. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply xonly_pubkey_save_entry.
   + exact Body.
   + reflexivity.
   + reflexivity.
 - split;[exact Storage|];split;[exact FreeF|];split;assumption.
Qed.

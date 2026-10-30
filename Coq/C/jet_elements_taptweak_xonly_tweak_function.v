(** Whole linked x-only tweak wrapper for represented valid affine keys. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements
 C.jet_sx_mem C.jet_secp_odd_table_literal_walk C.jet_secp_eckey_tweak_entry C.jet_secp_eckey_tweak_prepare C.jet_secp_eckey_tweak_finish
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
 C.jet_secp_canonical_scalar C.jet_secp_generator_pair_general C.jet_secp_generator_globals
 C.jet_secp_split_constants C.jet_secp_beta_global C.jet_secp_beta_state C.jet_secp_table_affine_nonzero
 C.jet_secp_curve_literal C.jet_secp_scalar_table_literal C.jet_secp_literal_gej_predicate C.jet_secp_gej_norm_literal
 C.jet_secp_modinfo_fe_caller C.jet_secp_modinfo_fe_transport C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_rescale_literal C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_memset_model C.jet_ctz_model C.jet_clight_forward C.jet_clight_internal_preserve C.jet_frame_inv C.jet_readBit_layout.
Require Import C.jet_secp_eckey_tweak_function C.jet_secp_tweak_bytes_entry C.jet_secp_tweak_bytes_calls
 C.jet_secp_scalar_set_canonical C.jet_secp_scalar_set_flag C.jet_secp_xonly_parse_field
 C.jet_secp_scalar_set_flag_frame C.jet_read8s_layout C.jet_sx_expr C.jet_sx_state
 C.jet_clight_internal_permissions.
Require Import C.jet_secp_statement_prefix C.jet_secp_tweak_bytes_function C.jet_secp_xonly_tweak_entry C.jet_secp_xonly_tweak_start C.jet_secp_xonly_tweak_calls
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_secp_storage_unpack C.jet_secp_pubkey_load_function
 C.jet_secp_pubkey_load_body C.jet_secp_pubkey_load_coordinates C.jet_secp_pubkey_save_function
 C.jet_secp_ge_storage_body C.jet_secp_ge_storage_function C.jet_secp_table_decode C.jet_secp_fe_b32 C.jet_memcpy_model.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_xonly_tweak_function C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo
 C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_beta
 C.jet_elements_taptweak_load_function C.jet_elements_taptweak_save C.jet_elements_taptweak_native_pure.
Require Import C.jet_elements_taptweak_tweak_bytes_function C.jet_elements_taptweak_xonly_tweak_entry
 C.jet_elements_taptweak_xonly_tweak_start C.jet_elements_taptweak_xonly_tweak_calls.
Local Opaque secp_ge elements_taptweak_ge eckey_tweak_value tweak_bytes_value tweak_bytes_result rescale_field_output.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem eval_elements_taptweak_xonly_pubkey_tweak_add (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (ng ax ay:Ty.tySem (Word 8)) w m bout bin bb:
 NoDup [bout;bin;bb] ->
 Mem.range_perm m bout 0 64 Cur Freeable ->Mem.range_perm m bin 0 64 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 (forall h,elements_taptweak_generator_table_state h m) ->elements_taptweak_split_ready m ->elements_taptweak_beta_initialized m ->elements_taptweak_modinfo_fe_state m ->
 affine_storage_readable m bin 0 w ->field_storage_value w=@toZ (WordToZ 8) ax ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->
 uint8_array_at m bb 0 (map Int.repr (xonly_input_bytes ng)) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_tweak_add)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf (Vint (bit_int (tweak_bytes_result ng ax ay))) /\
 xonly_tweak_saved_result (tweak_bytes_value ng ax ay) mf bout /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\Mem.range_perm mf bin 0 64 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bout /\b<>bb) m mf /\mem_forward m mf /\elements_taptweak_modinfo_fe_state mf /\readonly_preserved m mf.
Proof.
 intros Sep FO FI FB Tables Split Beta Ready Input ValueX ValueY Curve Bytes.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (FO 0);lia).
 assert (VI:Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (FI 0);lia).
 assert (VB:Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (FB 0);lia).
 destruct (elements_taptweak_xonly_tweak_entry m (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero) (Vptr bb Ptrofs.zero))
 as (mi & bk & Entry & Fresh & FKI & FrameI & KeepI & ReadI).
 assert (OK:bout<>bk) by (apply Fresh;exact VO).
 assert (IK:bin<>bk) by (apply Fresh;exact VI).
 assert (BK:bb<>bk) by (apply Fresh;exact VB).
 pose (e:=xonly_tweak_env bk);pose (le:=xonly_tweak_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero) (Vptr bb Ptrofs.zero)).
 assert (FOI:Mem.range_perm mi bout 0 64 Cur Freeable) by (intros pos Range;apply KeepI,FO;exact Range).
 assert (WeakI:Mem.weak_valid_pointer mi bin 0=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
   [apply KeepI,FI;clear;lia|apply perm_any_N]. }
 assert (WeakB:Mem.weak_valid_pointer mi bb 0=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
   [apply KeepI,FB;clear;lia|apply perm_any_N]. }
 destruct (exec_elements_taptweak_xonly_start Clear e le mi bout bin bb eq_refl eq_refl eq_refl eq_refl FOI WeakI WeakB)
 as (mz & Start & FOZ & KeepZ & FrameZ & ReadZ).
 assert (FKZ:Mem.range_perm mz bk 0 88 Cur Freeable) by (intros pos Range;apply KeepZ,FKI;exact Range).
 assert (InputZ:affine_storage_readable mz bin 0 w).
 { eapply affine_storage_readable_lframe;[|exact FrameZ|intros;distinct Sep].
   eapply affine_storage_readable_lframe;[exact Input|exact FrameI|intros;exact I]. }
 destruct (eval_elements_taptweak_xonly_pubkey_load Copy w mz bin 0 bk FKZ InputZ)
 as (ml & Load & Fields & Flag & FKL & FrameL & ReadL).
 rewrite (pubkey_storage_accept_curve w ax ay ValueX Curve) in Load.
 assert (FramePre:lframe (fun b _=>b<>bout /\b<>bk) m ml).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameI|intros;exact I].
   - eapply lframe_trans;
     [eapply lframe_implies;[exact FrameZ|intros b pos [NO NK] Old;exact NO]|
      eapply lframe_implies;[exact FrameL|intros b pos [NO NK] Old;exact NK]]. }
 assert (ReadPre:readonly_preserved m ml).
 { eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadZ|exact ReadL]. }
 assert (FOL:Mem.range_perm ml bout 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FOZ|exact FrameL|intros;exact OK]. }
 assert (FIL:Mem.range_perm ml bin 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FI|exact FramePre|intros;split;[distinct Sep|exact IK]]. }
 assert (FBL:Mem.range_perm ml bb 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FB|exact FramePre|intros;split;[distinct Sep|exact BK]]. }
 assert (BytesL:uint8_array_at ml bb 0 (map Int.repr (xonly_input_bytes ng))).
 { intros i v Nth;rewrite (proj1 FramePre Mint8unsigned bb (0+Z.of_nat i) VB);
   [apply Bytes;exact Nth|intros;split;[distinct Sep|exact BK]]. }
 assert (TablesL:forall h,elements_taptweak_generator_table_state h ml) by (intro h;eapply elements_taptweak_generator_readonly;[apply Tables|exact ReadPre]).
 assert (SplitL:elements_taptweak_split_ready ml) by (eapply elements_taptweak_split_readonly;[exact Split|exact ReadPre]).
 assert (BetaL:elements_taptweak_beta_initialized ml) by (eapply elements_taptweak_beta_initialized_preserved;[exact Beta|exact ReadPre]).
 assert (ReadyL:elements_taptweak_modinfo_fe_state ml).
 { eapply elements_taptweak_modinfo_readonly;[exact Ready|exact ReadPre]. }
 assert (TX:table_word_literal (affine_storage_coord w false) ax).
 { apply affine_storage_table_literal;exact ValueX. }
 assert (TY:table_word_literal (affine_storage_coord w true) ay).
 { apply affine_storage_table_literal;exact ValueY. }
 destruct (eval_elements_taptweak_bytes_helper Clear Count ng ax ay
  (affine_storage_coord w false) (affine_storage_coord w true) ml bk bb
  ltac:(congruence) FKL FBL TablesL SplitL BetaL ReadyL BytesL
  (affine_storage_square_bounds w false) (affine_storage_square_bounds w true) (Fields false) (Fields true) Flag TX TY Curve)
 as (mt & Tweak & PayloadT & FKT & FBT & FrameT & ForwardT & ReadyT & ReadT).
 pose (result:=tweak_bytes_result ng ax ay).
 pose proof (exec_elements_taptweak_xonly_test e le mz ml mt bk bin bb result eq_refl eq_refl eq_refl eq_refl eq_refl Load Tweak) as Test.
 assert (FOT:Mem.range_perm mt bout 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FOL|exact FrameT|intros;split;[exact OK|distinct Sep]]. }
 assert (FIT:Mem.range_perm mt bin 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FIL|exact FrameT|intros;split;[exact IK|distinct Sep]]. }
 assert (Finish:exists mb,
  Clight2.exec_stmt elements_taptweak_ge e le mz (Ssequence xonly_tweak_test xonly_tweak_finish) E0
  (xonly_tweak_test_temps le result) mb (Out_return (Some (Vint (bit_int result),tint))) /\
  xonly_tweak_saved_result (tweak_bytes_value ng ax ay) mb bout /\
  Mem.range_perm mb bout 0 64 Cur Freeable /\Mem.range_perm mb bin 0 64 Cur Freeable /\Mem.range_perm mb bb 0 32 Cur Freeable /\
  Mem.range_perm mb bk 0 88 Cur Freeable /\lframe (fun b _=>b<>bout) mt mb /\mem_forward mt mb /\readonly_preserved mt mb).
 { pose proof (tweak_bytes_result_option ng ax ay) as R;fold result in R.
   destruct (tweak_bytes_value ng ax ay) as [point|] eqn:Value.
   - assert (Yes:result=true) by exact R;rewrite Yes in Test.
     destruct PayloadT as (x & y & X & Y & BX & BY & FlagT & Pair).
     destruct (elements_taptweak_eval_pubkey_save Copy x y mt bk bout BX BY X Y FOT)
     as (mb & Save & Stored & FOB & FrameS & ReadS).
     exists mb;split.
     + rewrite Yes;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Test|].
       eapply exec_elements_taptweak_xonly_finish;try reflexivity;exact Save.
     + split.
       * exists x,y;split;[exact Stored|];split;[exact BX|];split;assumption.
       * split;[exact FOB|];split.
         -- eapply curve_keep_free;[clear;lia|exact FIT|exact FrameS|intros;distinct Sep].
         -- split.
            ++ eapply curve_keep_free;[clear;lia|exact FBT|exact FrameS|intros;distinct Sep].
            ++ split.
               ** eapply curve_keep_free;[clear;lia|exact FKT|exact FrameS|intros;clear -OK;congruence].
               ** split;[exact FrameS|];split;[exact(proj1 ReadS)|exact ReadS].
   - assert (No:result=false) by exact R;rewrite No in Test.
     exists mt;split.
     + rewrite No;eapply exec_Sseq_2;[exact Test|clear;discriminate].
     + split;[exact I|];split;[exact FOT|];split;[exact FIT|];split;[exact FBT|];split;[exact FKT|];
       split;[apply lframe_refl|];split;[apply mem_forward_refl|apply preserved_refl]. }
 destruct Finish as (mb & Tail & SavedB & FOB & FIB & FBB & FKB & FrameS & ForwardS & ReadS).
 destruct (elements_taptweak_single_point_free mb bk FKB) as (mf & Free & FrameF & ReadF).
 assert (Forward:mem_forward m mf).
 { eapply mem_forward_trans;[exact (proj1 ReadPre)|];eapply mem_forward_trans;[exact ForwardT|];
   eapply mem_forward_trans;[exact ForwardS|exact (proj1 ReadF)]. }
 assert (Frame:lframe (fun b _=>b<>bout /\b<>bb) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout /\b<>bb).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FramePre|intros b pos [Old [NO NB]] Valid;split;[exact NO|apply Fresh;exact Old]].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FrameT|intros b pos [Old [NO NB]] Valid;split;[apply Fresh;exact Old|exact NB]].
       * eapply lframe_trans;
          [eapply lframe_implies;[exact FrameS|intros b pos [Old [NO NB]] Valid;exact NO]|
           eapply lframe_implies;[exact FrameF|intros b pos [Old [NO NB]] Valid;apply Fresh;exact Old]].
   - intros b pos [NO NB] Old;repeat split;assumption. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=xonly_tweak_test_temps le result)
   (m1:=mi) (m2:=mb) (out:=Out_return (Some (Vint (bit_int result),tint))).
   + exact Entry.
   + rewrite xonly_tweak_body_source;eapply exec_statement_prefix_then_last;[exact Start|exact Tail].
   + split;[clear;discriminate|reflexivity].
   + exact Free.
 - split.
   + destruct (tweak_bytes_value ng ax ay) as [point|];[|exact I].
     destruct SavedB as (x & y & Stored & BX & BY & Pair);exists x,y;split.
     * eapply affine_storage_readable_lframe;[exact Stored|exact FrameF|intros;exact OK].
     * split;[exact BX|];split;assumption.
   + split.
     * eapply curve_keep_free;[clear;lia|exact FOB|exact FrameF|intros;exact OK].
     * split.
       -- eapply curve_keep_free;[clear;lia|exact FIB|exact FrameF|intros;exact IK].
       -- split.
          ++ eapply curve_keep_free;[clear;lia|exact FBB|exact FrameF|intros;exact BK].
          ++ split;[exact Frame|];split;[exact Forward|].
             split.
             ** eapply elements_taptweak_modinfo_readonly;[exact ReadyT|eapply preserved_trans;[exact ReadS|exact ReadF]].
             ** eapply preserved_trans;[exact ReadPre|];eapply preserved_trans;[exact ReadT|];
                eapply preserved_trans;[exact ReadS|exact ReadF].
Qed.

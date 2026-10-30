(** Linked TapTweak native suffix, all three guards, and exact output bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_root_chain_owned C.jet_secp_statement_prefix
 C.jet_sx_mem C.jet_sx_state C.jet_readBit_layout C.jet_read8s_layout C.jet_secp_fe_b32
 C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control C.jet_secp_xonly_tweak_function
 C.jet_secp_tweak_bytes_function C.jet_secp_tweak_group C.jet_secp_xonly_from_pubkey C.jet_secp_xonly_from_coordinates
 C.jet_secp_xonly_serialize C.jet_secp_pubkey_load_coordinates C.jet_secp_affine_storage C.jet_secp_storage_numeric
 C.jet_secp_canonical_normalize C.jet_secp_curve_literal C.jet_secp_curve_frame
 C.jet_secp_generator_globals C.jet_secp_split_constants C.jet_secp_beta_global C.jet_secp_modinfo_fe_caller
 C.jet_secp_modinfo_fe_transport C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model
 C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_taptweak_native C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals
 C.jet_elements_taptweak_modinfo C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_split_constants
 C.jet_elements_taptweak_beta C.jet_elements_taptweak_convert C.jet_elements_taptweak_serialize
 C.jet_elements_taptweak_parse_start.
Require Import C.jet_elements_taptweak_xonly_tweak_function.
Definition elements_taptweak_native_calls:=
 [(_secp256k1_xonly_pubkey_tweak_add,f_secp256k1_xonly_pubkey_tweak_add);
 (_secp256k1_xonly_pubkey_from_pubkey,f_secp256k1_xonly_pubkey_from_pubkey);
 (_secp256k1_xonly_pubkey_serialize,f_secp256k1_xonly_pubkey_serialize)].
Lemma elements_taptweak_native_calls_linked:
 map(secp_helper_lookup elements_taptweak_ge)elements_taptweak_native_calls=
 map(fun it=>Some(Internal(snd it)))elements_taptweak_native_calls.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma exec_elements_taptweak_native_call id fd result args vargs v e le m mf:
 In(id,fd)elements_taptweak_native_calls ->e!id=None ->
 eval_exprlist elements_taptweak_ge e le m args(type_of_params(fn_params fd))vargs ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal fd)vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m(curve_call id fd result args)E0(set_opttemp result v le)mf Out_normal.
Proof.
 intros Member Global Args Call.
 destruct(secp_helper_lookup_exists elements_taptweak_ge id fd
 (secp_map_eq_in _ _ _ elements_taptweak_native_calls_linked(id,fd)Member))as(bf & Symbol & Funct).
 eapply exec_elements_taptweak_curve_call with(bf:=bf);[exact Symbol| |exact Global|exact Args|exact Call].
 unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
Qed.
Local Opaque secp_ge elements_taptweak_ge canonical_fe_normalize tweak_bytes_value tweak_bytes_result.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_elements_taptweak_native (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (ng ax ay:Ty.tySem (Word 8)) w e le m bi bp bo bb:
 e!_input_pubkey=Some (bi,Tstruct __6478 noattr) ->e!_pubkey=Some (bp,Tstruct __2078 noattr) ->
 e!_output_pubkey=Some (bo,Tstruct __6478 noattr) ->e!_buf=Some (bb,tarray tuchar 32) ->
 e!_secp256k1_xonly_pubkey_tweak_add=None ->e!_secp256k1_xonly_pubkey_from_pubkey=None ->e!_secp256k1_xonly_pubkey_serialize=None ->
 NoDup [bi;bp;bo;bb] ->
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall h,elements_taptweak_generator_table_state h m) ->elements_taptweak_split_ready m ->elements_taptweak_beta_initialized m ->elements_taptweak_modinfo_fe_state m ->
 affine_storage_readable m bi 0 w ->field_storage_value w=@toZ (WordToZ 8) ax ->field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->
 uint8_array_at m bb 0 (map Int.repr (xonly_input_bytes ng)) ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m (statement_sequence taptweak_native_statements Sskip) E0
 (taptweak_native_temps le (tweak_bytes_result ng ax ay)) mf (taptweak_native_outcome (tweak_bytes_result ng ax ay)) /\
 taptweak_native_bytes (tweak_bytes_value ng ax ay) mf bb /\
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\b<>bo /\b<>bb) m mf /\mem_forward m mf /\elements_taptweak_modinfo_fe_state mf /\readonly_preserved m mf.
Proof.
 intros KI KP KO Buf TS CS SS Sep Owned Tables Split Beta Ready Input VX VY Curve Bytes.
 assert (FI:Mem.range_perm m bi 0 64 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FP:Mem.range_perm m bp 0 64 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FO:Mem.range_perm m bo 0 64 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FB:Mem.range_perm m bb 0 32 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (TweakSep:NoDup [bp;bi;bb]) by (clear -Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;repeat constructor;cbn [In];intuition congruence).
 destruct (eval_elements_taptweak_xonly_pubkey_tweak_add Copy Clear Count ng ax ay w m bp bi bb TweakSep FP FI FB
  Tables Split Beta Ready Input VX VY Curve Bytes)
 as (mt & Tweak & Payload & FPT & FIT & FBT & FrameT & ForwardT & ReadyT & ReadT).
 assert (FOT:Mem.range_perm mt bo 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FO|exact FrameT|intros;split;distinct Sep]. }
 pose (letw:=PTree.set _t'2 (Vint (bit_int (tweak_bytes_result ng ax ay))) le).
 assert (TweakStmt:Clight2.exec_stmt elements_taptweak_ge e le m taptweak_native_tweak E0 letw mt Out_normal).
 { unfold taptweak_native_tweak;eapply exec_elements_taptweak_native_call with
   (vargs:=[Vptr bp Ptrofs.zero;Vptr bi Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vint (bit_int (tweak_bytes_result ng ax ay))).
   - unfold elements_taptweak_native_calls;left;reflexivity.
   - exact TS.
   - eapply eval_Econs;[unfold taptweak_native_key;apply eval_Eaddrof;apply eval_Evar_local;exact KP|reflexivity|].
     eapply eval_Econs;[unfold taptweak_native_key;apply eval_Eaddrof;apply eval_Evar_local;exact KI|reflexivity|].
     eapply eval_Econs;[unfold taptweak_native_buf;eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|constructor].
   - exact Tweak. }
 pose proof (tweak_bytes_result_option ng ax ay) as Option.
 destruct (tweak_bytes_value ng ax ay) as [[x y]|] eqn:Value.
 - assert (Yes:tweak_bytes_result ng ax ay=true) by exact Option.
   unfold letw in TweakStmt;rewrite Yes in TweakStmt.
   pose (let1:=PTree.set _t'2 (Vint Int.one) le).
   destruct (xonly_tweak_saved_loadable ng ax ay x y mt bp Curve Value Payload)
    as (wt & StoredT & TX & TY & Accept).
   destruct (eval_elements_taptweak_xonly_from_pubkey_null Copy wt mt bo bp ltac:(distinct Sep) FOT FPT StoredT Accept)
    as (mc & Convert & SavedC & FOC & FPC & FrameC & ReadC).
   pose (let2:=PTree.set _t'3 (Vint Int.one) let1).
   assert (ConvertStmt:Clight2.exec_stmt elements_taptweak_ge e let1 mt taptweak_native_convert E0 let2 mc Out_normal).
   { unfold taptweak_native_convert;eapply exec_elements_taptweak_native_call with
     (vargs:=[Vptr bo Ptrofs.zero;Vlong Int64.zero;Vptr bp Ptrofs.zero]) (v:=Vint Int.one).
     - unfold elements_taptweak_native_calls;right;left;reflexivity.
     - exact CS.
     - eapply eval_Econs;[unfold taptweak_native_key;apply eval_Eaddrof;apply eval_Evar_local;exact KO|reflexivity|].
       eapply eval_Econs;[eapply eval_Ecast;[constructor|reflexivity]|reflexivity|].
       eapply eval_Econs;[unfold taptweak_native_key;apply eval_Eaddrof;apply eval_Evar_local;exact KP|reflexivity|constructor].
     - exact Convert. }
   destruct (xonly_from_saved_ready wt x y mc bo TX TY (tweak_bytes_value_curve ng ax ay x y Curve Value) SavedC)
    as (wc & outy & StoredC & CX & CY & CurveC).
   assert (FBC:Mem.range_perm mc bb 0 32 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FBT|exact FrameC|intros;distinct Sep]. }
   assert (FIC:Mem.range_perm mc bi 0 64 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FIT|exact FrameC|intros;distinct Sep]. }
   destruct (eval_elements_taptweak_xonly_serialize Copy Clear (@canonical_fe_normalize Simplicity.Alg.CoreFunSem x) outy wc mc bb bo
    ltac:(distinct Sep) FBC FOC StoredC CX CY CurveC)
    as (mf & Serialize & Output & FBF & FOF & FrameS & ReadS).
   pose (lef:=PTree.set _t'4 (Vint Int.one) let2).
   assert (SerializeStmt:Clight2.exec_stmt elements_taptweak_ge e let2 mc taptweak_native_serialize E0 lef mf Out_normal).
   { unfold taptweak_native_serialize;eapply exec_elements_taptweak_native_call with (vargs:=[Vptr bb Ptrofs.zero;Vptr bo Ptrofs.zero]) (v:=Vint Int.one).
     - unfold elements_taptweak_native_calls;right;right;left;reflexivity.
     - exact SS.
     - eapply eval_Econs;[unfold taptweak_native_buf;eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|].
       eapply eval_Econs;[unfold taptweak_native_key;apply eval_Eaddrof;apply eval_Evar_local;exact KO|reflexivity|constructor].
     - exact Serialize. }
   assert (FIF:Mem.range_perm mf bi 0 64 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FIC|exact FrameS|intros;distinct Sep]. }
   assert (FPF:Mem.range_perm mf bp 0 64 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FPC|exact FrameS|intros;distinct Sep]. }
   assert (Frame:lframe (fun b _=>b<>bp /\b<>bo /\b<>bb) m mf).
   { eapply lframe_trans;[eapply lframe_implies;[exact FrameT|intros b pos [NP [NO NB]] Old;split;assumption]|].
     eapply lframe_trans;
      [eapply lframe_implies;[exact FrameC|intros b pos [NP [NO NB]] Old;exact NO]|
       eapply lframe_implies;[exact FrameS|intros b pos [NP [NO NB]] Old;exact NB]]. }
   assert (Forward:mem_forward m mf).
   { eapply mem_forward_trans;[exact ForwardT|];eapply mem_forward_trans;[exact (proj1 ReadC)|exact (proj1 ReadS)]. }
   exists mf;split.
   + rewrite Yes;cbn [taptweak_native_temps taptweak_native_outcome statement_sequence taptweak_native_statements].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=let1).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact TweakStmt|apply exec_elements_taptweak_xonly_guard_one;apply PTree.gss].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=let2).
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact ConvertStmt|apply exec_elements_taptweak_xonly_guard_one;apply PTree.gss].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=lef).
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact SerializeStmt|apply exec_elements_taptweak_xonly_guard_one;apply PTree.gss].
          ++ constructor.
   + split;[exact Output|];split.
     * intros b hi Member;destruct Member as [Slot|[Slot|[Slot|[Slot|Empty]]]];try contradiction;
       inversion Slot;subst b hi;assumption.
     * split;[exact Frame|];split;[exact Forward|].
       split.
       -- eapply elements_taptweak_modinfo_readonly;[exact ReadyT|eapply preserved_trans;[exact ReadC|exact ReadS]].
       -- eapply preserved_trans;[exact ReadT|eapply preserved_trans;[exact ReadC|exact ReadS]].
 - assert (No:tweak_bytes_result ng ax ay=false) by exact Option.
   unfold letw in TweakStmt;rewrite No in TweakStmt.
   exists mt;split.
   + rewrite No;cbn [taptweak_native_temps taptweak_native_outcome statement_sequence taptweak_native_statements].
     eapply exec_Sseq_2.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact TweakStmt|apply exec_elements_taptweak_xonly_guard_zero;apply PTree.gss].
     * discriminate.
   + split;[exact I|];split.
     * intros b hi Member;destruct Member as [Slot|[Slot|[Slot|[Slot|Empty]]]];try contradiction;
       inversion Slot;subst b hi;assumption.
     * split.
       -- eapply lframe_implies;[exact FrameT|intros b pos [NP [NO NB]] Old;split;assumption].
       -- split;[exact ForwardT|];split;assumption.
Qed.

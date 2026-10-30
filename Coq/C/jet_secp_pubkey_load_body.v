(** Both zero-X outcomes of the original native-storage public-key loader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_pubkey_copy C.jet_secp_field_zero_readonly C.jet_secp_affine_storage
 C.jet_secp_affine_storage_frame C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_memcpy_model
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions C.jet_secp_closed_helpers.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition pubkey_load_decode:=curve_call _secp256k1_ge_from_storage f_secp256k1_ge_from_storage None
 [Etempvar _ge (tptr curve_ge_type);Eaddrof (Evar _s pubkey_storage_type) (tptr pubkey_storage_type)].
Definition pubkey_load_branch:=Ssequence pubkey_copy_stmt pubkey_load_decode.
Definition pubkey_load_size_test:=Ebinop Oeq (Esizeof pubkey_storage_type tulong) (Econst_int (Int.repr 64) tint) tint.
Definition pubkey_load_other:=match fn_body f_secp256k1_pubkey_load with
 |Ssequence (Sifthenelse _ _ other) _=>other|_=>Sskip end.
Definition pubkey_ge_x_address:=Eaddrof
 (Efield (Ederef (Etempvar _ge (tptr curve_ge_type)) curve_ge_type) _x curve_fe_type) (tptr curve_fe_type).
Definition pubkey_load_zero_call:=curve_call _secp256k1_fe_is_zero f_secp256k1_fe_is_zero (Some _t'1) [pubkey_ge_x_address].
Definition pubkey_load_zero_guard:=Sifthenelse
 (Eunop Onotbool (Eunop Onotbool (Etempvar _t'1 tint) tint) tint)
 (Sreturn (Some (Econst_int Int.zero tint))) Sskip.
Definition pubkey_load_tail:=Ssequence (Sloop (Ssequence pubkey_load_zero_call pubkey_load_zero_guard) Sbreak)
 (Sreturn (Some (Econst_int Int.one tint))).
Lemma pubkey_load_body_source:fn_body f_secp256k1_pubkey_load=
 Ssequence (Sifthenelse pubkey_load_size_test pubkey_load_branch pubkey_load_other) pubkey_load_tail.
Proof. reflexivity. Qed.
Lemma eval_pubkey_ge_x_address e le m bout:
 le!_ge=Some (Vptr bout Ptrofs.zero) ->eval_expr secp_ge e le m pubkey_ge_x_address (Vptr bout Ptrofs.zero).
Proof.
 intro Ge;destruct (curve_affine_layout _x 0 ltac:(left;reflexivity)) as (co & Layout & Offset).
 unfold pubkey_ge_x_address;apply eval_Eaddrof;rewrite <-(Ptrofs.add_zero_l Ptrofs.zero).
 eapply eval_Efield_struct with (co:=co) (delta:=0).
 - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact Ge|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Layout.
 - exact Offset.
Qed.
Definition pubkey_storage_accept w:=negb (Int64.eq (field_words_or (affine_storage_coord w false)) Int64.zero).
Theorem exec_pubkey_load_tail w e le m bout:
 le!_ge=Some (Vptr bout Ptrofs.zero) ->e!_secp256k1_fe_is_zero=None ->
 fe_at m bout 0 (words5 (affine_storage_coord w false)) ->Mem.range_perm m bout 0 40 Cur Freeable ->
 exists lef,Clight2.exec_stmt secp_ge e le m pubkey_load_tail E0 lef m
  (Out_return (Some (Vint (bit_int (pubkey_storage_accept w)),tint))).
Proof.
 intros Ge Symbol X Free.
 pose proof (eval_field_zero_readonly (affine_storage_coord w false) m bout X Free) as Zero.
 set (iszero:=Int64.eq (field_words_or (affine_storage_coord w false)) Int64.zero) in *.
 assert (Call:Clight2.exec_stmt secp_ge e le m pubkey_load_zero_call E0
  (PTree.set _t'1 (Vint (bit_int iszero)) le) m Out_normal).
 { unfold pubkey_load_zero_call;eapply exec_curve_call with
   (vargs:=[Vptr bout Ptrofs.zero]) (v:=Vint (bit_int iszero)).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact Symbol.
   - eapply eval_Econs;[apply eval_pubkey_ge_x_address;exact Ge|reflexivity|constructor].
   - destruct iszero;exact Zero. }
 exists (PTree.set _t'1 (Vint (bit_int iszero)) le).
 unfold pubkey_storage_accept;fold iszero;destruct iszero.
 - cbn [bit_int negb] in *;unfold pubkey_load_tail.
   eapply exec_Sseq_2 with (t1:=E0);[|discriminate].
   eapply exec_Sloop_stop1 with (out':=Out_return (Some (Vint Int.zero,tint)));[|constructor].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint Int.one) le);[exact Call|].
   unfold pubkey_load_zero_guard;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + eapply eval_Eunop;[eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity]|reflexivity].
   + reflexivity.
   + apply exec_Sreturn_some;constructor.
 - cbn [bit_int negb] in *;unfold pubkey_load_tail.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint Int.zero) le);[|apply exec_Sreturn_some;constructor].
   eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break) (t1:=E0) (t2:=E0).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
     (le1:=PTree.set _t'1 (Vint Int.zero) le);[exact Call|].
     unfold pubkey_load_zero_guard;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * eapply eval_Eunop;[eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity]|reflexivity].
     * reflexivity.
     * constructor.
   + constructor.
   + constructor.
   + constructor.
Qed.
Lemma pubkey_decode_allowed:allowed_call secp_closed_helpers (Internal f_secp256k1_ge_from_storage).
Proof. exists _secp256k1_ge_from_storage,f_secp256k1_ge_from_storage;split;vm_compute;reflexivity. Qed.
Theorem exec_pubkey_load_body (Model:memcpy_model) w e le m bin base bout bs bx b_y:
 e!_s=Some (bs,pubkey_storage_type) ->e!_memcpy=None ->
 e!_secp256k1_ge_from_storage=None ->e!_secp256k1_fe_is_zero=None ->
 le!_pubkey=Some (Vptr bin (Ptrofs.repr base)) ->le!_ge=Some (Vptr bout Ptrofs.zero) ->
 NoDup [bout;bs;bx;b_y] ->bin<>bs ->
 (forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 affine_storage_readable m bin base w ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_pubkey_load) E0 lef mf
  (Out_return (Some (Vint (bit_int (pubkey_storage_accept w)),tint))) /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 (forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bout /\b<>bs) m mf /\readonly_preserved m mf.
Proof.
 intros S CopySym DecodeSym ZeroSym Key Ge Separate SourceSep Owned Input.
 destruct (exec_pubkey_copy Model w e le m bin base bs S CopySym Key (not_eq_sym SourceSep)
  (Owned bs 64 ltac:(clear;cbn [In];tauto)) Input)
 as (mc & Copy & Storage & FreeS & FrameC & ReadC).
 assert (OutputSep:bout<>bs).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (OwnedC:forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mc b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (Pos.eq_dec b bs) as [Same|Other].
   - subst b;assert (Size:hi=64) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FreeS.
   - eapply curve_keep_free;[ |apply Owned;exact Slot|exact FrameC|intros;exact Other].
     clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia. }
 destruct (eval_ge_from_storage_readonly w mc bout bs 0 OutputSep
  (OwnedC bout 88 ltac:(clear;cbn [In];tauto)) Storage)
 as (md & Decode & FreeOut & Fields & Flag & Source & FrameD).
 assert (KeepD:keeps_permissions mc md).
 { exact (proj2 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok)
   _ _ _ _ _ _ Decode pubkey_decode_allowed). }
 assert (ReadD:readonly_preserved mc md).
 { exact (proj2 (internal_exec_preserved _ _ secp_closed_helpers_ok)
   _ _ _ _ _ _ Decode pubkey_decode_allowed). }
 destruct (exec_pubkey_load_tail w e le md bout Ge ZeroSym (Fields false)
  ltac:(intros pos Pos;apply FreeOut;lia)) as (lef & Tail).
 assert (DecodeCall:Clight2.exec_stmt secp_ge e le mc pubkey_load_decode E0 le md Out_normal).
 { unfold pubkey_load_decode;eapply exec_curve_call with
    (vargs:=[Vptr bout Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact DecodeSym.
   - eapply eval_Econs;[apply eval_Etempvar;exact Ge|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact S|reflexivity|constructor].
   - exact Decode. }
 exists md,lef;split.
 - rewrite pubkey_load_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);[|exact Tail].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + unfold pubkey_load_size_test;eapply eval_Ebinop;[apply eval_Esizeof|constructor|].
     change (Some (Vint Int.one)=Some (Vint Int.one));reflexivity.
   + reflexivity.
   + unfold pubkey_load_branch;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le);[exact Copy|exact DecodeCall].
 - split;[exact Fields|];split;[exact Flag|];split.
   + intros b hi Slot pos Pos;apply KeepD;exact (OwnedC b hi Slot pos Pos).
   + split.
     * eapply lframe_trans.
       { eapply lframe_implies;[exact FrameC|];intros b pos [_ Outside] _;exact Outside. }
       { apply curve_frame_two with (regs:=affine_storage_regs);[reflexivity|exact FrameD]. }
     * eapply preserved_trans;[exact ReadC|exact ReadD].
Qed.

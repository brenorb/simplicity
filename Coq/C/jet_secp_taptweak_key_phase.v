(** Compose the actual key read, SHA absorption and x-only parser, including failure. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_memcpy_model C.jet_memset_model
 C.jet_frame_inv C.jet_uint32_array_init C.jet_encoding C.jet_word_repr C.jet_input_layout C.jet_frame_layout C.jet_buffer_input
 C.jet_read8s_layout C.jet_sha_ctx8_model C.jet_secp_sha_absorb_short C.jet_secp_sha_startup
 C.jet_secp_taptweak_tag C.jet_secp_taptweak_io C.jet_secp_taptweak_parse
 C.jet_secp_public_byte_read C.jet_secp_word_bytes_codec C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control
 C.jet_secp_bip0340_public_parse C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_body
 C.jet_secp_generator_sha_start C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_root_chain_owned
 C.jet_clight_forward C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
(** A program-independent view of the context's actual fields. Unlike ctxi,
    it does not name the globals of the separate SHA translation unit. *)
Definition secp_sha_view m bc bs regs total bytes:=
 Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) /\uint32_array_at m bs 0 regs /\
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr total)) /\Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) /\
 (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i bytes Int.zero))).
Lemma secp_sha_view_framed m mf bc bs regs total bytes P:
 secp_sha_view m bc bs regs total bytes ->lframe P m mf ->
 (forall pos,P bc pos /\P bs pos) ->secp_sha_view mf bc bs regs total bytes.
Proof.
 intros (Pointer & State & Counter & Overflow & Buffer) Frame Outside.
 assert (VC:Mem.valid_block m bc) by (eapply load_valid;exact Pointer).
 split.
 - rewrite (proj1 Frame Mptr bc 0 VC);[exact Pointer|intros;apply (proj1 (Outside _))].
 - split.
   + intros i x Nth;pose proof (State i x Nth) as Load.
     rewrite (proj1 Frame Mint32 bs (0+4*Z.of_nat i) (load_valid _ _ _ _ _ Load));[exact Load|intros;apply (proj2 (Outside _))].
   + split.
     * rewrite (proj1 Frame Mint64 bc 8 VC);[exact Counter|intros;apply (proj1 (Outside _))].
     * split.
       -- rewrite (proj1 Frame Mint8unsigned bc 80 VC);[exact Overflow|intros;apply (proj1 (Outside _))].
       -- intros i Index;rewrite (proj1 Frame Mint8unsigned bc (16+Z.of_nat i) VC);[apply Buffer;exact Index|intros;apply (proj1 (Outside _))].
Qed.
Definition taptweak_key_absorb:=curve_call _sha256_uchars f_sha256_uchars None
 [Eaddrof (Evar _ctx__1 generator_sha_ctx_type) (tptr generator_sha_ctx_type);
 Evar _buf (tarray tuchar 32);Econst_int (Int.repr 32) tint].
Definition taptweak_key_phase:=Ssequence taptweak_key_read (Ssequence taptweak_key_absorb taptweak_parse_guard).
Lemma taptweak_key_phase_source:root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)=
 Ssequence taptweak_key_read (Ssequence taptweak_key_absorb
 (Ssequence taptweak_parse_guard (root_drop_statements 7 (fn_body f_simplicity_generic_taptweak)))).
Proof. reflexivity. Qed.
Local Opaque secp_ge Translate.encode.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_taptweak_key_phase (Copy:memcpy_model) (Clear:memset_model) (pk:Ty.tySem (Word 8))
 e le m bb bk bc bs bf bin edge cursor:
 e!_buf=Some (bb,tarray tuchar 32) ->e!_input_pubkey=Some (bk,Tstruct __6478 noattr) ->
 e!_ctx__1=Some (bc,generator_sha_ctx_type) ->e!_read8s=None ->e!_sha256_uchars=None ->e!_secp256k1_xonly_pubkey_parse=None ->
 le!_src=Some (Vptr bf Ptrofs.zero) ->NoDup [bb;bk;bc;bs;bf;bin] ->
 0<=cursor ->cursor+256<=Int64.max_unsigned ->
 (forall b hi,In (b,hi) [(bb,32);(bk,64);(bc,88);(bs,32);(bf,16)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 taptweak_startup m ->secp_sha_view m bc bs (state_regs taptweak_iv_word) 64 [] ->
 frame_fields_at m bf 0 bin edge cursor ->frame_input_cells_at m bin edge cursor (Translate.encode pk) ->exists mf,
 Clight2.exec_stmt secp_ge e le m taptweak_key_phase E0
 (PTree.set _t'1 (Vint (xonly_parse_result pk)) le) mf (bip0340_parse_outcome pk) /\
 xonly_parsed_result pk mf bk /\secp_sha_view mf bc bs (state_regs taptweak_iv_word) 96 (schnorr_word_bytes pk) /\
 frame_fields_at mf bf 0 bin edge (cursor+256) /\
 (forall b hi,In (b,hi) [(bb,32);(bk,64);(bc,88);(bs,32);(bf,16)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bf /\b<>bb /\b<>bc /\b<>bk) m mf /\readonly_preserved m mf /\taptweak_startup mf.
Proof.
 intros Buf Key Context RG AG PG Source Sep Cursor Max Owned Startup SHA Fields Input.
 assert (FB:Mem.range_perm m bb 0 32 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FK:Mem.range_perm m bk 0 64 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FC:Mem.range_perm m bc 0 88 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FS:Mem.range_perm m bs 0 32 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FF:Mem.range_perm m bf 0 16 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 pose (xs:=vector_values (Word 3) 5 pk).
 assert (Length:length xs=32%nat) by (unfold xs;apply vector_values_length).
 destruct (eval_secp_public_byte_read xs m bb bf bin edge cursor
 ltac:(rewrite Length;change (32<=18446744073709551615);clear;lia) Cursor
 ltac:(rewrite Length;exact Max) ltac:(distinct Sep) ltac:(distinct Sep) ltac:(distinct Sep)
 ltac:(rewrite Length;exact FB) FF Fields ltac:(unfold xs;rewrite <-encode_vector_values;exact Input)) as
 (mr & Read & BytesR & FieldsR & KeepR & FrameR & ReadR).
 rewrite Length in Read,FieldsR.
 change (uint8_array_at mr bb 0 (schnorr_word_bytes pk)) in BytesR.
 assert (OwnedR:forall b hi,In (b,hi) [(bb,32);(bk,64);(bc,88);(bs,32);(bf,16)] ->Mem.range_perm mr b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepR;apply (Owned b hi Slot);exact Range. }
 assert (SHAR:secp_sha_view mr bc bs (state_regs taptweak_iv_word) 64 []).
 { eapply secp_sha_view_framed;[exact SHA|exact FrameR|intros;repeat split;distinct Sep]. }
 assert (StartupR:taptweak_startup mr).
 { eapply taptweak_startup_owned_forward with (slots:=[(bf,16);(bb,32)]);
 [exact Startup|exact (proj1 ReadR)| |].
 - intros b hi [Pair|[Pair|[]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact FrameR|intros b pos Outside Valid;cbn [map fst In] in Outside;cbn;intuition congruence]. }
 destruct SHAR as (PointerR & StateR & CounterR & OverflowR & BufferR).
 assert (SourceBytes:forall i,(i<length (schnorr_word_bytes pk))%nat ->
 Mem.load Mint8unsigned mr bb (Ptrofs.unsigned Ptrofs.zero+Z.of_nat i)=Some (Vint (nth i (schnorr_word_bytes pk) Int.zero))).
 { intros i Index;apply BytesR;apply nth_error_nth';exact Index. }
 destruct (eval_secp_sha_absorb_short_counter Copy [] (schnorr_word_bytes pk) 64 mr bc bb Ptrofs.zero (Vptr bs Ptrofs.zero)
 ltac:(rewrite schnorr_word_bytes_length;cbn;lia) ltac:(lia) ltac:(rewrite schnorr_word_bytes_length;cbn;lia) eq_refl
 ltac:(distinct Sep) (proj2 (proj2 (proj1 StartupR))) (OwnedR bc 88 ltac:(clear;cbn [In];tauto))
 ltac:(rewrite schnorr_word_bytes_length;change (32<=18446744073709551615);lia)
 PointerR CounterR OverflowR BufferR SourceBytes) as
 (ma & Absorb & PointerA & CounterA & OverflowA & BufferA & FCA & FrameA & ReadA & SHAA).
 rewrite schnorr_word_bytes_length in Absorb,CounterA.
 assert (OwnedA:forall b hi,In (b,hi) [(bb,32);(bk,64);(bc,88);(bs,32);(bf,16)] ->Mem.range_perm ma b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [In] in Slot;repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
 match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;try assumption.
 all:eapply curve_keep_free;[clear;lia|apply OwnedR;clear;cbn [In];tauto|exact FrameA|intros;distinct Sep]. }
 assert (VSR:Mem.valid_block mr bs) by (eapply Mem.perm_valid_block;apply (OwnedR bs 32 ltac:(clear;cbn [In];tauto) 0);clear;lia).
 assert (StateA:uint32_array_at ma bs 0 (state_regs taptweak_iv_word)).
 { intros i x Nth;rewrite (proj1 FrameA Mint32 bs (0+4*Z.of_nat i) VSR);[apply StateR;exact Nth|intros;distinct Sep]. }
 assert (SHAvA:secp_sha_view ma bc bs (state_regs taptweak_iv_word) 96 (schnorr_word_bytes pk)).
 { split;[exact PointerA|];split;[exact StateA|];split;[exact CounterA|];split;[exact OverflowA|exact BufferA]. }
 assert (StartupA:taptweak_startup ma).
 { eapply taptweak_startup_owned_forward with (slots:=[(bc,88)]);
 [exact StartupR|exact (proj1 ReadA)| |].
 - intros b hi [Pair|[]];inversion Pair;subst;split;[clear;lia|apply OwnedR;clear;cbn [In];tauto].
 - eapply lframe_implies;[exact FrameA|intros b pos Outside Valid;cbn [map fst In] in Outside;cbn;intuition congruence]. }
 assert (BytesA:uint8_array_at ma bb 0 (map Int.repr (xonly_input_bytes pk))).
 { unfold xonly_input_bytes;rewrite word256_serializer_bytes.
 eapply uint8_array_framed;[exact BytesR|exact FrameA|intros;distinct Sep]. }
 destruct (exec_taptweak_parse Copy Clear pk e le ma bk bb Key Buf PG ltac:(distinct Sep)
 (OwnedA bk 64 ltac:(clear;cbn [In];tauto)) (OwnedA bb 32 ltac:(clear;cbn [In];tauto)) BytesA) as
 (mf & Parse & Parsed & FKF & FBF & FrameP & ReadP).
 assert (OwnedF:forall b hi,In (b,hi) [(bb,32);(bk,64);(bc,88);(bs,32);(bf,16)] ->Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [In] in Slot;repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
 match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;try assumption.
 all:eapply curve_keep_free;[clear;lia|apply OwnedA;clear;cbn [In];tauto|exact FrameP|intros;split;distinct Sep]. }
 assert (SHAF:secp_sha_view mf bc bs (state_regs taptweak_iv_word) 96 (schnorr_word_bytes pk)).
 { eapply secp_sha_view_framed;[exact SHAvA|exact FrameP|intros;repeat split;distinct Sep]. }
 assert (StartupF:taptweak_startup mf).
 { eapply taptweak_startup_owned_forward with (slots:=[(bk,64);(bb,32)]);
 [exact StartupA|exact (proj1 ReadP)| |].
 - intros b hi [Pair|[Pair|[]]];inversion Pair;subst;split;[clear;lia|apply OwnedA;clear;cbn [In];tauto|clear;lia|apply OwnedA;clear;cbn [In];tauto].
 - eapply lframe_implies;[exact FrameP|intros b pos Outside Valid;cbn [map fst In] in Outside;cbn;intuition congruence]. }
 assert (VF:Mem.valid_block mr bf) by (eapply Mem.perm_valid_block;apply (OwnedR bf 16 ltac:(clear;cbn [In];tauto) 0);clear;lia).
 assert (FieldsA:frame_fields_at ma bf 0 bin edge (cursor+256)).
 { destruct FieldsR as [Edge Count];split;rewrite (proj1 FrameA) by (try exact VF;intros;distinct Sep);assumption. }
 assert (VFA:Mem.valid_block ma bf) by (eapply Mem.perm_valid_block;apply (OwnedA bf 16 ltac:(clear;cbn [In];tauto) 0);clear;lia).
 assert (FieldsF:frame_fields_at mf bf 0 bin edge (cursor+256)).
 { destruct FieldsA as [Edge Count];split;rewrite (proj1 FrameP) by (try exact VFA;intros;split;distinct Sep);assumption. }
 exists mf;split.
 - unfold taptweak_key_phase;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr).
   + eapply exec_taptweak_key_read;[exact RG|exact Buf|exact Source|exact Read].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma);[|exact Parse].
     unfold taptweak_key_absorb;eapply exec_schnorr_challenge_call with
     (vargs:=[Vptr bc Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong (Int64.repr 32)]) (v:=Vint Int.one).
     * right;left;reflexivity.
     * exact AG.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
       eapply eval_Econs.
       { eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]. }
       { reflexivity. }
       eapply eval_Econs;[constructor|reflexivity|constructor].
     * exact Absorb.
 - split;[exact Parsed|];split;[exact SHAF|];split;[exact FieldsF|];split;[exact OwnedF|];split.
   + eapply lframe_trans.
     { eapply lframe_implies;[exact FrameR|intros b pos (NF & NB & NC & NK) Valid;split;assumption]. }
     eapply lframe_trans; eapply lframe_implies;
     [exact FrameA|intros b pos (NF & NB & NC & NK) Valid;exact NC|
      exact FrameP|intros b pos (NF & NB & NC & NK) Valid;split;assumption].
   + split;[eapply preserved_trans;[exact ReadR|eapply preserved_trans;[exact ReadA|exact ReadP]]|exact StartupF].
Qed.

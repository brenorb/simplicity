(** Compose the original input-hash reader and the three remaining SHA calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_memcpy_model C.jet_uint32_array_init
 C.jet_encoding C.jet_frame_layout C.jet_frame_inv C.jet_read8s_layout C.jet_sha_ctx8_model
 C.jet_secp_taptweak_key_phase C.jet_secp_taptweak_tag C.jet_secp_taptweak_hash C.jet_secp_public_hash_read
 C.jet_secp_generator_sha_start C.jet_secp_curve_frame C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_hash_phase:=Ssequence (secp_local_hash_read _input_hash) taptweak_message_hash_stmt.
Local Opaque secp_ge Translate.encode.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_taptweak_hash_phase (Copy:memcpy_model) (pk h:Ty.tySem (Word 8)) e le m bb bc bs bt bf bin edge cursor:
 e!_buf=Some (bb,tarray tuchar 32) ->e!_ctx__1=Some (bc,generator_sha_ctx_type) ->
 e!_output_hash=Some (bs,generator_sha_state_type) ->e!_input_hash=Some (bt,generator_sha_state_type) ->
 e!_read32s=None ->e!_sha256_hash=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
 le!_src=Some (Vptr bf Ptrofs.zero) ->NoDup [bb;bc;bs;bt;bf;bin] ->0<=cursor ->cursor+256<=Int64.max_unsigned ->
 (forall b hi,In (b,hi) [(bb,32);(bc,88);(bs,32);(bt,32);(bf,16)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 taptweak_startup m ->secp_sha_view m bc bs (state_regs taptweak_iv_word) 96 (C.jet_secp_schnorr_challenge_hash.schnorr_word_bytes pk) ->
 frame_fields_at m bf 0 bin edge cursor ->frame_input_cells_at m bin edge cursor (Translate.encode h) ->exists mf,
 Clight2.exec_stmt secp_ge e le m taptweak_hash_phase E0 le mf Out_normal /\
 uint8_array_at mf bb 0 (C.jet_secp_schnorr_challenge_hash.schnorr_word_bytes (taptweak_hash_word pk h)) /\
 uint32_array_at mf bs 0 (state_regs (taptweak_hash_word pk h)) /\
 uint32_array_at mf bt 0 (state_regs h) /\frame_fields_at mf bf 0 bin edge (cursor+256) /\
 (forall b hi,In (b,hi) [(bb,32);(bc,88);(bs,32);(bt,32);(bf,16)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bf /\b<>bt /\b<>bc /\b<>bs /\b<>bb) m mf /\readonly_preserved m mf /\taptweak_startup mf.
Proof.
 intros Buf Context State InputHash RG HG FG DG Source Sep Cursor Max Owned Startup SHA Fields Input.
 assert (FT:Mem.range_perm m bt 0 32 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (FF:Mem.range_perm m bf 0 16 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 destruct (eval_secp_public_hash_read h m bt bf bin edge cursor Cursor Max ltac:(distinct Sep)
 ltac:(distinct Sep) ltac:(distinct Sep) FT FF Fields Input) as
 (mr & Read & Words & FieldsR & KeepR & FrameR & ReadR).
 assert (OwnedR:forall b hi,In (b,hi) [(bb,32);(bc,88);(bs,32);(bt,32);(bf,16)] ->Mem.range_perm mr b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepR;apply (Owned b hi Slot);exact Range. }
 assert (SHAR:secp_sha_view mr bc bs (state_regs taptweak_iv_word) 96 (C.jet_secp_schnorr_challenge_hash.schnorr_word_bytes pk)).
 { eapply secp_sha_view_framed;[exact SHA|exact FrameR|intros;repeat split;distinct Sep]. }
 assert (StartupR:taptweak_startup mr).
 { eapply taptweak_startup_owned_forward with (slots:=[(bf,16);(bt,32)]);
 [exact Startup|exact (proj1 ReadR)| |].
 - intros b hi [Pair|[Pair|[]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact FrameR|intros b pos Outside Valid;cbn [map fst In] in Outside;cbn;intuition congruence]. }
 destruct SHAR as (PointerR & StateR & CounterR & OverflowR & BufferR).
 assert (HashSep:NoDup [bc;bs;bt;bb]).
 { clear -Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;repeat constructor;cbn [In];intuition congruence. }
 destruct (eval_taptweak_message_hash Copy pk h mr bc bs bt bb HashSep (proj2 (proj2 (proj1 StartupR)))
 (OwnedR bc 88 ltac:(clear;cbn [In];tauto)) (OwnedR bs 32 ltac:(clear;cbn [In];tauto))
 (OwnedR bt 32 ltac:(clear;cbn [In];tauto)) (OwnedR bb 32 ltac:(clear;cbn [In];tauto))
 Words PointerR StateR CounterR OverflowR ltac:(rewrite <-(C.jet_secp_schnorr_challenge_hash.schnorr_word_bytes_length pk);exact BufferR)) as
 (m1 & m2 & mf & Hash & Finalize & Digest & BytesF & StateF & PointerF & CounterF & OverflowF & FCF & FSF & FTF & FBF & InputF & FrameH & ReadH & SHAF).
 assert (HashBody:Clight2.exec_stmt secp_ge e le mr taptweak_message_hash_stmt E0 le mf Out_normal).
 { eapply exec_taptweak_hash_calls;[exact HG|exact FG|exact DG|exact Context|exact State|exact InputHash|exact Buf|exact Hash|exact Finalize|exact Digest]. }
 assert (OwnedF:forall b hi,In (b,hi) [(bb,32);(bc,88);(bs,32);(bt,32);(bf,16)] ->Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [In] in Slot;repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
 match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;try assumption.
 eapply curve_keep_free;[clear;lia|apply OwnedR;clear;cbn [In];tauto|exact FrameH|intros;repeat split;distinct Sep]. }
 assert (StartupF:taptweak_startup mf).
 { eapply taptweak_startup_owned_forward with (slots:=[(bc,88);(bs,32);(bb,32)]);
 [exact StartupR|exact (proj1 ReadH)| |].
 - intros b hi [Pair|[Pair|[Pair|[]]]];inversion Pair;subst;split;try (clear;lia);apply OwnedR;clear;cbn [In];tauto.
 - eapply lframe_implies;[exact FrameH|intros b pos Outside Valid;cbn [map fst In] in Outside;cbn;intuition congruence]. }
 assert (VF:Mem.valid_block mr bf) by (eapply Mem.perm_valid_block;apply (OwnedR bf 16 ltac:(clear;cbn [In];tauto) 0);clear;lia).
 assert (FieldsF:frame_fields_at mf bf 0 bin edge (cursor+256)).
 { destruct FieldsR as [Edge Count];split;rewrite (proj1 FrameH) by (try exact VF;intros;repeat split;distinct Sep);assumption. }
 exists mf;split.
 - unfold taptweak_hash_phase;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr);[|exact HashBody].
   eapply exec_secp_local_hash_read;[exact RG|exact InputHash|exact Source|exact Read].
 - split;[exact BytesF|];split;[exact StateF|];split;[exact InputF|];split;[exact FieldsF|];split;[exact OwnedF|];split.
   + eapply lframe_trans;
     [eapply lframe_implies;[exact FrameR|intros b pos (NF & NT & NC & NS & NB) Valid;split;assumption]|
      eapply lframe_implies;[exact FrameH|intros b pos (NF & NT & NC & NS & NB) Valid;repeat split;assumption]].
   + split;[eapply preserved_trans;[exact ReadR|exact ReadH]|exact StartupF].
Qed.

(** Original CheckSig message block: tag constructor, copy, read and SHA suffix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate
 C.jets_secp C.jet_secp_linkage C.jet_secp_checksig_public_entry C.jet_secp_checksig_context
 C.jet_secp_checksig_tag C.jet_secp_checksig_tagged C.jet_secp_checksig_hash C.jet_secp_checksig_hash_calls
 C.jet_secp_public_pair_read C.jet_secp_bip0340_data_reads C.jet_secp_root_chain_owned
 C.jet_secp_schnorr_challenge_owned C.jet_secp_schnorr_challenge_absorb C.jet_secp_schnorr_challenge_hash
 C.jet_secp_schnorr_startup C.jet_secp_sha_startup C.jet_memcpy_model C.jet_sha_ctx8_model
 C.jet_uint32_array_init C.jet_read8s_layout C.jet_sx_mem C.jet_input_layout C.jet_frame_layout
 C.jet_frame_inv C.jet_encoding C.jet_buffer_input C.jet_clight_internal_preserve C.jet_word_repr.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition checksig_message_block:=Ssequence checksig_context_setup
 (Ssequence (bip0340_read_bytes _msg 64) checksig_hash_calls).
Lemma checksig_message_source:
 match root_drop_statements 3 (fn_body f_simplicity_check_sig_verify) with
 | Ssequence message _=>message|_=>Sskip end=checksig_message_block.
Proof. reflexivity. Qed.
Local Opaque secp_ge Translate.encode.
Local Ltac distinct Sep:=clear -Sep;unfold checksig_public_locals in Sep;
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence.
Local Ltac original_owner Owner:=apply Owner;clear;cbn [checksig_public_storage In];tauto.
Theorem exec_checksig_message_block (Model:memcpy_model) (ir h:Ty.tySem (Word 8)) le m
 bl bb bkey bmsg bsig bout bctx bres bi edge cursor:
 NoDup (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres) ->
 ~In bi (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres) ->
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->checksig_startup m ->
 0<=cursor ->cursor+512<=Int64.max_unsigned ->
 frame_fields_at m bl 0 bi edge cursor ->
 frame_input_cells_at m bi edge cursor (@Translate.encode (Word 9) (ir,h)) ->exists mf,
 Clight2.exec_stmt secp_ge (checksig_public_env bl bb bkey bmsg bsig bout bctx bres) le m
 checksig_message_block E0 le mf Out_normal /\
 schnorr_bytes_at mf bb Ptrofs.zero (schnorr_word_bytes (checksig_hash_word ir h)) /\
 frame_fields_at mf bl 0 bi edge (cursor+512) /\
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bl /\b<>bb /\b<>bmsg /\b<>bout /\b<>bctx /\b<>bres) m mf /\
 readonly_preserved m mf /\checksig_startup mf.
Proof.
 intros Separate InputApart Owned Ready Cursor Max Fields Input.
 destruct (exec_checksig_context_setup Model (checksig_public_env bl bb bkey bmsg bsig bout bctx bres)
  le m bctx bres bout eq_refl eq_refl eq_refl eq_refl eq_refl
  ltac:(repeat constructor;cbn [In];distinct Separate) Ready
  ltac:(original_owner Owned) ltac:(original_owner Owned) ltac:(original_owner Owned))
 as (mt & Setup & PointerT & CounterT & OverflowT & StateT & FCT & FRT & FOT & FrameT & ReadT & ReadyT).
 assert (OwnedT:forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->
  Mem.range_perm mt b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [checksig_public_storage In] in Slot;
   repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;subst b hi;
   first [exact FCT|exact FRT|exact FOT|
    eapply schnorr_owner_framed;[lia|exact FrameT|intros;repeat split;distinct Separate|original_owner Owned]]. }
 assert (FieldsT:frame_fields_at mt bl 0 bi edge cursor).
 { destruct Fields as [Edge Count];split.
   - rewrite (proj1 FrameT Mptr bl 0 (load_valid _ _ _ _ _ Edge));[exact Edge|intros;repeat split;distinct Separate].
   - rewrite (proj1 FrameT Mint64 bl (0+8) (load_valid _ _ _ _ _ Count));[exact Count|intros;repeat split;distinct Separate]. }
 assert (InputT:frame_input_cells_at mt bi edge cursor (@Translate.encode (Word 9) (ir,h))).
 { eapply buffer_input_cells_preserved;[|exact Input].
   intros ofs w Load;rewrite (proj1 FrameT Mint64 bi ofs (load_valid _ _ _ _ _ Load));[exact Load|].
   intros;clear -InputApart;unfold checksig_public_locals in InputApart;cbn [In] in InputApart;intuition congruence. }
 destruct (exec_secp_public_pair_read ir h _msg (checksig_public_env bl bb bkey bmsg bsig bout bctx bres)
  le mt bmsg bl bi edge cursor eq_refl eq_refl eq_refl Cursor Max
  ltac:(distinct Separate)
  ltac:(clear -InputApart;unfold checksig_public_locals in InputApart;cbn [In] in InputApart;intuition congruence)
  ltac:(clear -InputApart;unfold checksig_public_locals in InputApart;cbn [In] in InputApart;intuition congruence)
  (OwnedT bmsg 64 ltac:(clear;cbn [checksig_public_storage In];tauto))
  (OwnedT bl 16 ltac:(clear;cbn [checksig_public_storage In];tauto)) FieldsT InputT)
 as (mr & Read & BytesR & FieldsR & KeepR & FrameR & ReadR).
 assert (OwnedR:forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->
  Mem.range_perm mr b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepR;exact (OwnedT b hi Slot pos Range). }
 assert (ReadyR:checksig_startup mr).
 { eapply checksig_startup_owned_forward with (slots:=[(bl,16);(bmsg,64)]);
   [exact ReadyT|exact (proj1 ReadR)| |].
   - intros b hi Slot;destruct Slot as [Slot|[Slot|Empty]];try contradiction;inversion Slot;subst;split;try lia;apply OwnedT;clear;cbn [checksig_public_storage In];tauto.
   - eapply lframe_implies;[exact FrameR|];intros b pos Outside Old;cbn [map fst In] in Outside;split;intuition congruence. }
 assert (PointerR:Mem.load Mptr mr bctx 0=Some (Vptr bout Ptrofs.zero)).
 { rewrite (proj1 FrameR);[exact PointerT|eapply load_valid;exact PointerT|intros;split;distinct Separate]. }
 assert (CounterR:Mem.load Mint64 mr bctx 8=Some (Vlong (Int64.repr 64))).
 { rewrite (proj1 FrameR);[exact CounterT|eapply load_valid;exact CounterT|intros;split;distinct Separate]. }
 assert (OverflowR:Mem.load Mint8unsigned mr bctx 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameR);[exact OverflowT|eapply load_valid;exact OverflowT|intros;split;distinct Separate]. }
 assert (StateR:uint32_array_at mr bout 0 (state_regs checksig_iv_word)).
 { intros i v Nth;rewrite (proj1 FrameR);[exact (StateT i v Nth)|eapply Mem.perm_valid_block;apply (FOT 0);lia|intros;split;distinct Separate]. }
 destruct (exec_checksig_hash_calls Model ir h (checksig_public_env bl bb bkey bmsg bsig bout bctx bres) le mr
  bctx bout bmsg bb eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  ltac:(distinct Separate) ltac:(distinct Separate) ltac:(distinct Separate) ltac:(distinct Separate)
  (proj2 (proj2 (proj1 ReadyR)))
  (OwnedR bctx 88 ltac:(clear;cbn [checksig_public_storage In];tauto))
  (OwnedR bout 32 ltac:(clear;cbn [checksig_public_storage In];tauto))
  (OwnedR bb 32 ltac:(clear;cbn [checksig_public_storage In];tauto))
  PointerR StateR CounterR OverflowR)
 as (mf & Hash & Message & FCF & FOF & FBF & FrameF & ReadF & SHAF).
 { intros i Index;rewrite Ptrofs.unsigned_zero,Z.add_0_l;apply BytesR;apply nth_error_nth';exact Index. }
 assert (OwnedF:forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->
  Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [checksig_public_storage In] in Slot;
   repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;subst b hi;
   first [exact FCF|exact FOF|exact FBF|
    eapply schnorr_owner_framed;[lia|exact FrameF|intros;repeat split;distinct Separate|
     apply OwnedR;clear;cbn [checksig_public_storage In];tauto]]. }
 exists mf;split.
 - unfold checksig_message_block;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=le);[exact Setup|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le);[exact Read|exact Hash].
 - split;[exact Message|];split.
   + destruct FieldsR as [Edge Count];split.
     * rewrite (proj1 FrameF Mptr bl 0 (load_valid _ _ _ _ _ Edge));[exact Edge|intros;repeat split;distinct Separate].
     * rewrite (proj1 FrameF Mint64 bl (0+8) (load_valid _ _ _ _ _ Count));[exact Count|intros;repeat split;distinct Separate].
   + split;[exact OwnedF|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameT|intros b pos (L & B & M & O & C & R) Old;repeat split;assumption].
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact FrameR|intros b pos (L & B & M & O & C & R) Old;split;assumption].
          ++ eapply lframe_implies;[exact FrameF|intros b pos (L & B & M & O & C & R) Old;repeat split;assumption].
     * split;[eapply preserved_trans;[exact ReadT|eapply preserved_trans;[exact ReadR|exact ReadF]]|].
       eapply checksig_startup_owned_forward with (slots:=[(bctx,88);(bout,32);(bb,32)]);
       [exact ReadyR|exact (proj1 ReadF)| |].
       -- intros b hi Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;subst;split;try lia;apply OwnedR;clear;cbn [checksig_public_storage In];tauto.
       -- eapply lframe_implies;[exact FrameF|];intros b pos Outside Old;cbn [map fst In] in Outside;repeat split;intuition congruence.
Qed.

(** All original CheckSig statements after a successful public-key parse. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout C.jet_readBit_layout C.jet_sx_mem
 C.jet_buffer_input C.jet_frame_inv C.jet_read8s_layout C.jet_word_repr
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame C.jet_secp_root_chain_owned
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_clight_forward C.jet_clight_internal_preserve
 C.jet_secp_schnorr_verify_literal C.jet_secp_schnorr_startup C.jet_secp_linear_startup
 C.jet_secp_sha_startup C.jet_secp_modinfo_fe_caller C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_field
 C.jet_secp_schnorr_verify_parsed C.jet_secp_schnorr_challenge_owned
 C.jet_secp_checksig_tag C.jet_secp_checksig_tagged C.jet_secp_checksig_hash C.jet_secp_checksig_message
 C.jet_secp_checksig_public_entry C.jet_secp_checksig_verifier_return
 C.jet_secp_public_pair_read C.jet_secp_bip0340_data_reads C.jet_secp_public_byte_read
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb C.jet_secp_word_bytes_codec.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma checksig_after_parse_source:root_drop_statements 3 (fn_body f_simplicity_check_sig_verify)=
 Ssequence checksig_message_block (Ssequence (bip0340_read_bytes _sig 64) checksig_verifier_return).
Proof. reflexivity. Qed.
Local Opaque secp_ge literal_bip0340_check Translate.encode.
Local Ltac distinct Sep:=clear -Sep;unfold checksig_public_locals in Sep;
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence.
Theorem exec_checksig_after_parse (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk ir h r s:Ty.tySem (Word 8)) le m bl bb bkey bmsg bsig bout bctx bres bi edge cursor:
 NoDup (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres) ->
 ~In bi (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres) ->
 0<=cursor ->cursor+1280<=Int64.max_unsigned ->
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 frame_fields_at m bl 0 bi edge (cursor+256) ->
 frame_input_cells_at m bi edge (cursor+256) (@Translate.encode (Word 9) (ir,h)) ->
 frame_input_cells_at m bi edge (cursor+768) (@Translate.encode (Word 9) (r,s)) ->
 xonly_parse_result pk=Int.one ->xonly_parsed_result pk m bkey ->checksig_startup m ->exists mf lef,
 Clight2.exec_stmt secp_ge (checksig_public_env bl bb bkey bmsg bsig bout bctx bres) le m
 (root_drop_statements 3 (fn_body f_simplicity_check_sig_verify)) E0 lef mf
 (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,checksig_hash_word ir h),(r,s))))),tint))) /\
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) m mf /\
 mem_forward m mf /\checksig_startup mf.
Proof.
 intros Separate InputApart Cursor Max Owned Source MsgInput SigInput Success Parsed Ready.
 assert (Slots:forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->
  0<hi /\Mem.range_perm m b 0 hi Cur Freeable).
 { intros b hi Slot;split;[clear -Slot;cbn [checksig_public_storage In] in Slot;
   repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia|exact (Owned b hi Slot)]. }
 destruct (exec_checksig_message_block Copy ir h le m bl bb bkey bmsg bsig bout bctx bres bi edge (cursor+256)
  Separate InputApart Owned Ready ltac:(lia) ltac:(lia) Source MsgInput)
 as (mm & Message & MsgBytes & FieldsM & OwnedM & FrameM & ReadM & ReadyM).
 assert (ParsedM:xonly_parsed_result pk mm bkey).
 { eapply xonly_parsed_result_framed;[exact Parsed|exact FrameM|intros;repeat split;distinct Separate]. }
 assert (SigInputM:frame_input_cells_at mm bi edge (cursor+768) (@Translate.encode (Word 9) (r,s))).
 { eapply buffer_input_cells_preserved;[|exact SigInput].
   intros ofs w Load;rewrite (proj1 FrameM Mint64 bi ofs (load_valid _ _ _ _ _ Load));[exact Load|].
   intros;clear -InputApart;unfold checksig_public_locals in InputApart;cbn [In] in InputApart;intuition congruence. }
 replace (cursor+256+512) with (cursor+768) in FieldsM by lia.
 destruct (exec_secp_public_pair_read r s _sig (checksig_public_env bl bb bkey bmsg bsig bout bctx bres)
  le mm bsig bl bi edge (cursor+768) eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia)
  ltac:(distinct Separate)
  ltac:(clear -InputApart;unfold checksig_public_locals in InputApart;cbn [In] in InputApart;intuition congruence)
  ltac:(clear -InputApart;unfold checksig_public_locals in InputApart;cbn [In] in InputApart;intuition congruence)
  (OwnedM bsig 64 ltac:(clear;cbn [checksig_public_storage In];tauto))
  (OwnedM bl 16 ltac:(clear;cbn [checksig_public_storage In];tauto)) FieldsM SigInputM)
 as (md & ReadSig & SigBytes & FieldsD & KeepD & FrameD & ReadD).
 destruct (uint8_array_split_app md bsig 0 _ _ SigBytes) as [RBytes SBytes].
 rewrite schnorr_word_bytes_length in SBytes;change (uint8_array_at md bsig 32 (schnorr_word_bytes s)) in SBytes.
 assert (RInput:uint8_array_at md bsig 0 (map Int.repr (xonly_input_bytes r))).
 { unfold xonly_input_bytes;rewrite word256_serializer_bytes;exact RBytes. }
 assert (SInput:uint8_array_at md bsig 32 (map Int.repr (xonly_input_bytes s))).
 { unfold xonly_input_bytes;rewrite word256_serializer_bytes;exact SBytes. }
 assert (ParsedD:xonly_parsed_result pk md bkey).
 { eapply xonly_parsed_result_framed;[exact ParsedM|exact FrameD|intros;split;distinct Separate]. }
 assert (MsgBytesD:schnorr_bytes_at md bb Ptrofs.zero (schnorr_word_bytes (checksig_hash_word ir h))).
 { eapply schnorr_bytes_framed;[exact FrameD| |intros;split;distinct Separate|exact MsgBytes].
   eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact MsgBytes]. }
 assert (OwnedD:forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm md b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepD;exact (OwnedM b hi Slot pos Range). }
 assert (FrameMD:lframe (fun b _=>~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) m md).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameM|];intros b pos Outside Old;clear -Outside;unfold checksig_public_locals in Outside;cbn [In] in *;intuition congruence.
   - eapply lframe_implies;[exact FrameD|];intros b pos Outside Old;clear -Outside;unfold checksig_public_locals in Outside;cbn [In] in *;intuition congruence. }
 assert (ForwardMD:mem_forward m md) by (eapply mem_forward_trans;[exact (proj1 ReadM)|exact (proj1 ReadD)]).
 assert (ReadyD:checksig_startup md).
 { eapply checksig_startup_owned_forward;[exact Ready|exact ForwardMD|exact Slots|exact FrameMD]. }
 destruct (proj1 ReadyD) as ([Split [Beta Tables]] & Modulus & SHA).
 destruct (exec_checksig_verifier_return Copy Clear Count pk (checksig_hash_word ir h) r s
  (checksig_public_env bl bb bkey bmsg bsig bout bctx bres) le md bsig bb bkey
  eq_refl eq_refl eq_refl eq_refl ltac:(distinct Separate) ltac:(distinct Separate)
  (OwnedD bsig 64 ltac:(clear;cbn [checksig_public_storage In];tauto)) RInput SInput MsgBytesD Success ParsedD
  SHA Tables Split Beta Modulus)
 as (mf & Return & SigFree & FrameF & ForwardF).
 assert (Frame:lframe (fun b _=>~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) m mf).
 { eapply lframe_trans;[exact FrameMD|];eapply lframe_implies;[exact FrameF|].
   intros b pos Outside Old;clear -Outside;unfold checksig_public_locals in Outside;cbn [In] in *;intuition congruence. }
 assert (Forward:mem_forward m mf) by (eapply mem_forward_trans;[exact ForwardMD|exact ForwardF]).
 exists mf,(PTree.set _t'2 (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,checksig_hash_word ir h),(r,s)))))) le);split.
 - rewrite checksig_after_parse_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mm) (le1:=le);[exact Message|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);[exact ReadSig|exact Return].
 - split.
   + intros b hi Slot;destruct (Pos.eq_dec b bsig) as [Same|Other].
     * subst b;assert (Size:hi=64).
       { clear -Slot Separate;unfold checksig_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;
         cbn [checksig_public_storage In] in *;intuition congruence. }
       subst hi;exact SigFree.
     * eapply curve_keep_free;[|exact (OwnedD b hi Slot)|exact FrameF|intros;exact Other].
       exact (proj1 (Slots b hi Slot)).
   + split;[exact Frame|];split;[exact Forward|].
     eapply checksig_startup_owned_forward;[exact Ready|exact Forward|exact Slots|exact Frame].
Qed.

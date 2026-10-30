(** All original generic body phases at the linked GE, with the actual Elements tag/hash. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_frame_inv C.jet_frame_spec C.jet_frame_layout
 C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_buffer_input C.jet_word_repr
 C.jet_read8s_layout C.jet_sha_ctx8_model C.jet_uint32_array_init C.jet_readBit_layout
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_secp_curve_frame
 C.jet_secp_taptweak_entry C.jet_secp_taptweak_tag C.jet_secp_taptweak_writer_state C.jet_secp_taptweak_body_prefix
 C.jet_secp_taptweak_key_phase C.jet_secp_taptweak_hash_phase C.jet_secp_taptweak_hash
 C.jet_secp_taptweak_parsed_native C.jet_secp_taptweak_finish C.jet_secp_taptweak_phase_glue
 C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_result C.jet_secp_bip0340_public_parse
 C.jet_secp_decompress_literal C.jet_secp_affine_storage C.jet_secp_table_decode C.jet_secp_schnorr_challenge_hash C.jet_secp_sha_init_copy
 C.jet_secp_statement_prefix C.jet_secp_root_chain_owned C.jet_clight_forward C.jet_clight_internal_preserve.
Require Simplicity.Alg.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_taptweak_body C.jet_elements_taptweak_pure C.jet_elements_taptweak_tag
 C.jet_elements_taptweak_key_phase C.jet_elements_taptweak_hash_phase C.jet_elements_taptweak_message_hash.
Require Import C.jet_elements_taptweak_runtime_ready C.jet_elements_taptweak_initial_phase C.jet_elements_taptweak_finish
 C.jet_taptweak_phase_glue_at.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_runtime_tag_block taptweak_value taptweak_result taptweak_output elements_taptweak_hash_word elements_taptweak_iv_word.
Local Ltac distinct Sep:=clear -Sep;unfold taptweak_locals in Sep;cbn [app] in Sep;
 repeat rewrite NoDup_cons_iff in Sep;repeat rewrite not_in_cons in Sep;cbn [In] in *;intuition congruence.
Local Ltac notlocal Outside:=clear -Outside;cbn [taptweak_body_locals taptweak_locals app In] in *;intuition congruence.
Theorem exec_elements_taptweak_body (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk h:Ty.tySem (Word 8)) le m bb bi bo bp bt bh bs bc bc1 br br1 bf bin edge rc bd base bw outedge cursor:
 le!_tagName__3=Some (Vptr elements_taptweak_runtime_tag_block Ptrofs.zero) ->le!_tagLen=Some (Vlong (Int64.repr 17)) ->
 le!_src=Some (Vptr bf Ptrofs.zero) ->le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1++[bf;bin]) ->
 ~In bd (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf) ->
 ~In bw (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf) ->
 (forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 elements_taptweak_runtime_ready m ->0<=rc ->rc+512<=Int64.max_unsigned ->frame_fields_at m bf 0 bin edge rc ->
 frame_input_cells_at m bin edge rc (@Translate.encode (Word 9) (pk,h)) ->write_frame_at m bd base bw outedge cursor 256 ->exists mf lef,
 Clight2.exec_stmt elements_taptweak_ge (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) le m (fn_body f_simplicity_generic_taptweak)
 E0 lef mf (Out_return (Some (Vint (bit_int (taptweak_result (elements_taptweak_hash_word pk h) pk)),tint))) /\
 (match taptweak_output (elements_taptweak_hash_word pk h) pk with None=>True|Some value=>
 frame_output_cells_at mf bw outedge cursor (Translate.encode value) /\write_prefix_at m mf bw outedge cursor /\frame_fields_at mf bd base bw outedge (cursor-256) end) /\
 (forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf) /\b<>bd /\b<>bw) m mf /\
 (forall chunk b ofs,Mem.valid_block m b ->~In b (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf) ->
 (b<>bd \/ofs+size_chunk chunk<=base+8 \/base+16<=ofs) ->
 (b<>bw \/ofs+size_chunk chunk<=outedge+8*((cursor-256)/64) \/write_word_address outedge cursor+8<=ofs) ->
 Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\mem_forward m mf /\elements_taptweak_runtime_ready mf.
Proof.
 intros Name Len Source Dest Sep OldD OldW Owned Ready RC Max Fields Input Output.
 assert (Unique:NoDup (map fst (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf))).
 { rewrite taptweak_body_slots_map;exact (@NoDup_app_remove_r block
 (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf) [bin] Sep). }
 assert (BinOutside:~In bin (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf)).
 { pose proof (@NoDup_remove_2 block (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf) [] bin Sep) as Outside;
 rewrite app_nil_r in Outside;exact Outside. }
 assert (PrivateSep:NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)).
 { exact (@NoDup_app_remove_r block (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1) [bf;bin] Sep). }
 assert (OldPositive:forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable).
 { intros b hi Slot;split;[eapply taptweak_body_slots_positive;exact Slot|apply Owned;exact Slot]. }
 change (frame_input_cells_at m bin edge rc (Translate.encode pk++Translate.encode h)) in Input.
 apply frame_input_cells_at_app in Input;destruct Input as [InputPK InputH];rewrite (encode_word_length 8 pk) in InputH.
 destruct (exec_elements_taptweak_initial_phase Copy le m bb bi bo bp bt bh bs bc bc1 br br1 Name Len PrivateSep
 ltac:(intros b hi Slot;apply Owned;apply in_or_app;left;exact Slot) Ready) as
 (mp & Init & TagP & StateP & PointerP & CounterP & OverflowP & OwnedPrivateP & FrameP & ReadP & StartupP).
 assert(ReadyP:elements_taptweak_runtime_ready mp)by exact StartupP.
 assert (OwnedP:forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm mp b 0 hi Cur Freeable).
 { eapply owned_slots_after with (changed:=taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1);
 [exact Unique|exact OldPositive|intros b hi Slot;apply in_or_app;left;exact Slot|exact OwnedPrivateP|exact FrameP|].
 intros b hi Slot Other pos;cbn [taptweak_storage map fst In] in Other;repeat split;intuition congruence. }
 assert (ExternalP:lframe (fun b _=>~In b (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf)) m mp).
 { eapply lframe_implies;[exact FrameP|intros b pos Outside Valid;repeat split;notlocal Outside]. }
 assert (FieldsP:frame_fields_at mp bf 0 bin edge rc).
 { destruct Fields as [Edge Offset];pose proof (load_valid _ _ _ _ _ Edge) as VF;
 split;rewrite (proj1 FrameP) by (try exact VF;intros;repeat split;distinct Sep);assumption. }
 assert (InputPKP:frame_input_cells_at mp bin edge rc (Translate.encode pk)).
 { eapply buffer_input_cells_preserved;[|exact InputPK];intros ofs w Load;
 rewrite (proj1 ExternalP Mint64 bin ofs (load_valid _ _ _ _ _ Load));[exact Load|intros;exact BinOutside]. }
 assert (SHAP:secp_sha_view mp bc1 bs (state_regs elements_taptweak_iv_word) 64 []).
 { rewrite <-elements_taptweak_iv_word_regs in StateP;split;[exact PointerP|];split;[exact StateP|];split;[exact CounterP|];split;[exact OverflowP|intros i Impossible;inversion Impossible]. }
 assert (KeySep:NoDup [bb;bi;bc1;bs;bf;bin]).
 { clear -Sep;unfold taptweak_locals in *;cbn [app] in *;repeat rewrite NoDup_cons_iff in *;repeat rewrite not_in_cons in *;cbn [In] in *;
 repeat constructor;cbn [In];intuition congruence. }
 destruct (exec_elements_taptweak_key_phase Copy Clear pk (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) le mp
 bb bi bc1 bs bf bin edge rc eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Source KeySep RC ltac:(lia)
 ltac:(intros b hi Slot;apply OwnedP;clear -Slot;cbn [taptweak_body_storage taptweak_storage app In] in *;tauto)
 (proj1(proj2 ReadyP)) SHAP FieldsP InputPKP) as
 (mk & Key & ParsedK & SHAK & FieldsK & OwnedKey & FrameK & ReadK & StartupK).
 assert(ReadyK:elements_taptweak_runtime_ready mk).
 { eapply elements_taptweak_runtime_ready_owned with(slots:=[(bb,32);(bi,64);(bc1,88);(bs,32);(bf,16)]);[exact ReadyP|exact ReadK| |].
   - intros b hi Member;split.
     + clear -Member;cbn[In]in Member;repeat destruct Member as[Same|Member];try contradiction;injection Same as <- <-;lia.
     + apply OwnedP;clear -Member;cbn[taptweak_body_storage taptweak_storage app In]in *;tauto.
   - eapply lframe_implies;[exact FrameK|intros b pos Outside Valid;clear -Outside;cbn[map fst In]in Outside|-*;intuition congruence]. }
 assert (OwnedK:forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm mk b 0 hi Cur Freeable).
 { eapply owned_slots_after with (changed:=[(bb,32);(bi,64);(bc1,88);(bs,32);(bf,16)]);
 [exact Unique| | |exact OwnedKey|exact FrameK|].
 - intros b hi Slot;split;[eapply taptweak_body_slots_positive;exact Slot|apply OwnedP;exact Slot].
 - intros b hi Slot;clear -Slot;cbn [taptweak_body_storage taptweak_storage app In] in *;tauto.
 - intros b hi Slot Other pos;cbn [map fst In] in Other;repeat split;intuition congruence. }
 assert (ExternalK:lframe (fun b _=>~In b (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf)) m mk).
 { eapply lframe_trans;[exact ExternalP|];eapply lframe_implies;[exact FrameK|].
 intros b pos Outside Valid;repeat split;notlocal Outside. }
 assert (ForwardK:mem_forward m mk) by (eapply mem_forward_trans;[exact (proj1 ReadP)|exact (proj1 ReadK)]).
 destruct (xonly_parse_result_cases pk) as [Failure|Success].
 - rewrite Failure in Key;unfold bip0340_parse_outcome in Key;rewrite Failure in Key.
   destruct (taptweak_key_failure_value (elements_taptweak_hash_word pk h) pk Failure) as [Value Result].
   exists mk,(PTree.set _t'1 (Vint Int.zero) le);rewrite Result;split.
   + eapply(exec_taptweak_initial_then_at elements_taptweak_ge);[exact Init|];eapply(exec_taptweak_key_aborts_at elements_taptweak_ge);[discriminate|exact Key].
   + split;[rewrite Value;exact I|];split;[exact OwnedK|];split.
     * eapply lframe_implies;[exact ExternalK|intros b pos [Outside _] Valid;exact Outside].
     * split.
       -- intros chunk b ofs Valid Outside OD OW;apply (proj1 ExternalK);[exact Valid|intros;exact Outside].
       -- split;[exact ForwardK|exact ReadyK].
 - rewrite Success in Key;unfold bip0340_parse_outcome in Key;rewrite Success in Key.
   pose (lek:=PTree.set _t'1 (Vint Int.one) le).
   assert (InputHK:frame_input_cells_at mk bin edge (rc+256) (Translate.encode h)).
   { eapply buffer_input_cells_preserved;[|exact InputH];intros ofs w Load;
     rewrite (proj1 ExternalK Mint64 bin ofs (load_valid _ _ _ _ _ Load));[exact Load|intros;exact BinOutside]. }
   assert (HashSep:NoDup [bb;bc1;bs;bh;bf;bin]).
   { clear -Sep;unfold taptweak_locals in *;cbn [app] in *;repeat rewrite NoDup_cons_iff in *;repeat rewrite not_in_cons in *;cbn [In] in *;
   repeat constructor;cbn [In];intuition congruence. }
   assert (SrcK:lek!_src=Some (Vptr bf Ptrofs.zero)) by (unfold lek;rewrite PTree.gso by discriminate;exact Source).
   destruct (exec_elements_taptweak_hash_phase Copy pk h (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) lek mk
    bb bc1 bs bh bf bin edge (rc+256) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl SrcK HashSep ltac:(lia) ltac:(lia)
    ltac:(intros b hi Slot;apply OwnedK;clear -Slot;cbn [taptweak_body_storage taptweak_storage app In] in *;tauto)
    (proj1(proj2 ReadyK)) SHAK FieldsK InputHK) as (mh & Hash & BytesH & StateH & InputHWords & FieldsH & OwnedHash & FrameH & ReadH & StartupH).
   assert(ReadyH:elements_taptweak_runtime_ready mh).
 { eapply elements_taptweak_runtime_ready_owned with(slots:=[(bb,32);(bc1,88);(bs,32);(bh,32);(bf,16)]);[exact ReadyK|exact ReadH| |].
   - intros b hi Member;split.
     + clear -Member;cbn[In]in Member;repeat destruct Member as[Same|Member];try contradiction;injection Same as <- <-;lia.
     + apply OwnedK;clear -Member;cbn[taptweak_body_storage taptweak_storage app In]in *;tauto.
   - eapply lframe_implies;[exact FrameH|intros b pos Outside Valid;clear -Outside;cbn[map fst In]in Outside|-*;intuition congruence]. }
   assert (OwnedH:forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm mh b 0 hi Cur Freeable).
   { eapply owned_slots_after with (changed:=[(bb,32);(bc1,88);(bs,32);(bh,32);(bf,16)]);
   [exact Unique| | |exact OwnedHash|exact FrameH|].
   - intros b hi Slot;split;[eapply taptweak_body_slots_positive;exact Slot|apply OwnedK;exact Slot].
   - intros b hi Slot;clear -Slot;cbn [taptweak_body_storage taptweak_storage app In] in *;tauto.
   - intros b hi Slot Other pos;cbn [map fst In] in Other;repeat split;intuition congruence. }
   assert (ParsedH:xonly_parsed_result pk mh bi).
   { intros Bound ax ay Decoded;destruct (ParsedK Bound ax ay Decoded) as (w & Stored & X & Y).
   exists w;split;[|split;assumption];eapply affine_storage_readable_lframe;[exact Stored|exact FrameH|intros;repeat split;distinct Sep]. }
   assert (ExternalH:lframe (fun b _=>~In b (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf)) m mh).
   { eapply lframe_trans;[exact ExternalK|];eapply lframe_implies;[exact FrameH|].
   intros b pos Outside Valid;repeat split;notlocal Outside. }
   assert (ForwardH:mem_forward m mh) by (eapply mem_forward_trans;[exact ForwardK|exact (proj1 ReadH)]).
   assert (OutputH:write_frame_at mh bd base bw outedge cursor 256).
   { eapply write_frame_at_framed;[exact Output|exact ExternalH|intros;split;assumption]. }
   assert (FinishSep:NoDup [bi;bp;bo;bb]).
   { clear -Sep;unfold taptweak_locals in *;cbn [app] in *;repeat rewrite NoDup_cons_iff in *;repeat rewrite not_in_cons in *;cbn [In] in *;
   repeat constructor;cbn [In];intuition congruence. }
   assert (DstK:lek!_dst=Some (Vptr bd (Ptrofs.repr base))) by (unfold lek;rewrite PTree.gso by discriminate;exact Dest).
   destruct (exec_elements_taptweak_finish Copy Clear Count (elements_taptweak_hash_word pk h) pk
    (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) lek mh bi bp bo bb bd base bw outedge cursor
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl DstK FinishSep
    ltac:(clear -OldD;cbn [taptweak_body_locals taptweak_locals app In] in *;intuition)
    ltac:(clear -OldW;cbn [taptweak_body_locals taptweak_locals app In] in *;intuition)
    ltac:(intros b hi Slot;apply OwnedH;clear -Slot;cbn [taptweak_body_storage taptweak_storage app In] in *;tauto)
    Success ParsedH ReadyH BytesH OutputH) as (mf & Finish & ObserveF & OwnedFinish & FrameF & LoadsF & ForwardF & ReadyF & ReadF).
   assert (OwnedF:forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm mf b 0 hi Cur Freeable).
   { eapply owned_slots_after with (changed:=[(bi,64);(bp,64);(bo,64);(bb,32)]);
   [exact Unique| | |exact OwnedFinish|exact FrameF|].
   - intros b hi Slot;split;[eapply taptweak_body_slots_positive;exact Slot|apply OwnedH;exact Slot].
   - intros b hi Slot;clear -Slot;cbn [taptweak_body_storage taptweak_storage app In] in *;tauto.
   - intros b hi Slot Other pos;split;[exact Other|];split;intro Same;subst b;
     [apply OldD|apply OldW];eapply taptweak_body_member;exact Slot. }
   exists mf,(C.jet_secp_taptweak_native.taptweak_native_temps lek (taptweak_result (elements_taptweak_hash_word pk h) pk));split.
   + eapply(exec_taptweak_initial_then_at elements_taptweak_ge);[exact Init|];eapply(exec_taptweak_key_then_at elements_taptweak_ge);[exact Key|];
     eapply(exec_taptweak_hash_then_at elements_taptweak_ge);[exact Hash|exact Finish].
   + split.
     * destruct (taptweak_output (elements_taptweak_hash_word pk h) pk) as [value|];[|exact I].
       destruct ObserveF as (Cells & Prefix & CursorF);split;[exact Cells|];split;[|exact CursorF].
       eapply write_prefix_at_preserved with (mr:=mh) (me:=mf);[|intros;assumption|exact Prefix].
       intros ofs w Load;rewrite (proj1 ExternalH Mint64 bw ofs (load_valid _ _ _ _ _ Load));[exact Load|intros;exact OldW].
     * split;[exact OwnedF|];split.
       -- eapply lframe_trans.
          { eapply lframe_implies;[exact ExternalH|intros b pos [Outside _] Valid;exact Outside]. }
          eapply lframe_implies;[exact FrameF|intros b pos [Outside [ND NW]] Valid;split;[|split;assumption];notlocal Outside].
       -- split.
          ++ intros chunk b ofs Valid Outside OD OW;rewrite LoadsF.
             ** apply (proj1 ExternalH);[exact Valid|intros;exact Outside].
             ** exact (proj1 (ForwardH b Valid)).
             ** notlocal Outside.
             ** exact OD.
             ** exact OW.
          ++ split;[eapply mem_forward_trans;[exact ForwardH|exact ForwardF]|exact ReadyF].
Qed.

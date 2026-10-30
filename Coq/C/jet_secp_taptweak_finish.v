(** Complete original native-tweak-to-return suffix, with rejection and exact output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_frame_inv C.jet_frame_spec C.jet_frame_layout
 C.jet_output_layout C.jet_write_layout C.jet_bitcoin_effects C.jet_read8s_layout C.jet_buffer_input C.jet_encoding
 C.jet_write8_sequence C.jet_write8s_layout C.jet_secp_frame C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model
 C.jet_secp_taptweak_native C.jet_secp_taptweak_parsed_native C.jet_secp_taptweak_writer_state C.jet_secp_taptweak_io
 C.jet_secp_xonly_parse_field C.jet_secp_schnorr_challenge_hash C.jet_secp_word_bytes_codec
 C.jet_secp_fe_b32 C.jet_secp_canonical_normalize C.jet_secp_curve_frame C.jet_secp_statement_prefix
 C.jet_secp_root_chain_owned C.jet_clight_forward C.jet_clight_internal_preserve.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_output (ng pk:Ty.tySem (Word 8)):=
 option_map (fun xy=>@canonical_fe_normalize Simplicity.Alg.CoreFunSem (fst xy)) (taptweak_value ng pk).
Lemma write_frame_at_framed m mf bd base bw edge cursor count P:
 write_frame_at m bd base bw edge cursor count ->lframe P m mf ->
 (forall pos,P bd pos /\P bw pos) ->write_frame_at mf bd base bw edge cursor count.
Proof.
 intros (Base & Fields & Edge & Count & Max & Cursor & Writes) Frame Outside.
 assert (VD:Mem.valid_block m bd) by (eapply load_valid;exact (proj1 Fields)).
 split;[exact Base|];split.
 - destruct Fields as [Word Cur];split;rewrite (proj1 Frame) by (try exact VD;intros;apply (proj1 (Outside _)));assumption.
 - split;[exact Edge|];split;[exact Count|];split;[exact Max|];split.
   + destruct Cursor as [Permission Align];split;[|exact Align].
     intros pos Range;apply (proj1 (proj2 Frame));[exact VD|apply (proj1 (Outside _))|apply Permission;exact Range].
   + intros i Index;destruct (Writes i Index) as (Low & High & Apart & Permission & w & Load).
     assert (VW:Mem.valid_block m bw) by (eapply load_valid;exact Load).
     split;[exact Low|];split;[exact High|];split;[exact Apart|];split.
     * destruct Permission as [Permission Align];split;[|exact Align].
       intros pos Range;apply (proj1 (proj2 Frame));[exact VW|apply (proj2 (Outside _))|apply Permission;exact Range].
     * exists w;rewrite (proj1 Frame) by (try exact VW;intros;apply (proj2 (Outside _)));exact Load.
Qed.
Lemma taptweak_native_destination le result:(taptweak_native_temps le result)!_dst=le!_dst.
Proof. destruct result;unfold taptweak_native_temps;rewrite !PTree.gso by discriminate;reflexivity. Qed.
Local Opaque secp_ge Translate.encode canonical_fe_normalize taptweak_value taptweak_result.
Theorem exec_taptweak_finish (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (ng pk:Ty.tySem (Word 8)) e le m bi bp bo bb bd base bw edge cursor:
 e!_input_pubkey=Some (bi,Tstruct __6478 noattr) ->e!_pubkey=Some (bp,Tstruct __2078 noattr) ->
 e!_output_pubkey=Some (bo,Tstruct __6478 noattr) ->e!_buf=Some (bb,tarray tuchar 32) ->
 e!_secp256k1_xonly_pubkey_tweak_add=None ->e!_secp256k1_xonly_pubkey_from_pubkey=None ->
 e!_secp256k1_xonly_pubkey_serialize=None ->e!_write8s=None ->le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 NoDup [bi;bp;bo;bb] ->~In bd [bi;bp;bo;bb] ->~In bw [bi;bp;bo;bb] ->
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 xonly_parse_result pk=Int.one ->xonly_parsed_result pk m bi ->taptweak_ready m ->
 uint8_array_at m bb 0 (schnorr_word_bytes ng) ->write_frame_at m bd base bw edge cursor 256 ->exists mf,
 Clight2.exec_stmt secp_ge e le m (root_drop_statements 11 (fn_body f_simplicity_generic_taptweak)) E0
 (taptweak_native_temps le (taptweak_result ng pk)) mf
 (Out_return (Some (Vint (C.jet_readBit_layout.bit_int (taptweak_result ng pk)),tint))) /\
 (match taptweak_output ng pk with None=>True|Some value=>
 frame_output_cells_at mf bw edge cursor (Translate.encode value) /\write_prefix_at m mf bw edge cursor /\
 frame_fields_at mf bd base bw edge (cursor-256) end) /\
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b [bi;bp;bo;bb] /\b<>bd /\b<>bw) m mf /\
 (forall chunk b ofs,Mem.valid_block m b ->~In b [bi;bp;bo;bb] ->
 (b<>bd \/ofs+size_chunk chunk<=base+8 \/base+16<=ofs) ->
 (b<>bw \/ofs+size_chunk chunk<=edge+8*((cursor-256)/64) \/write_word_address edge cursor+8<=ofs) ->
 Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\mem_forward m mf /\taptweak_ready mf.
Proof.
 intros KI KP KO Buf TG CG SG WG Dest Sep OldD OldW Owned Success Parsed Ready Bytes Output.
 destruct (exec_taptweak_parsed_native Copy Clear Count ng pk e le m bi bp bo bb KI KP KO Buf TG CG SG
 Sep Owned Success Parsed (proj1 Ready) Bytes) as (mn & Native & Payload & OwnedN & FrameN & ForwardN & StartupN).
 assert (ReadyN:taptweak_ready mn) by (eapply taptweak_ready_forward;[exact Ready|exact StartupN|exact ForwardN]).
 pose proof (taptweak_result_option ng pk) as Option.
 destruct (taptweak_value ng pk) as [[x y]|] eqn:Value.
 - change (taptweak_result ng pk=Datatypes.true) in Option;rewrite Option in Native.
   pose (ox:=@canonical_fe_normalize Simplicity.Alg.CoreFunSem x).
   assert (Buffer:uint8_array_at mn bb 0 (schnorr_word_bytes ox)).
   { unfold taptweak_native_bytes in Payload;change (uint8_array_at mn bb 0 (map Int.repr (C.jet_secp_fe_b32.be_bytes (@toZ (WordToZ 8) ox)))) in Payload.
     rewrite word256_serializer_bytes in Payload;exact Payload. }
   assert (OutputN:write_frame_at mn bd base bw edge cursor 256).
   { eapply write_frame_at_framed;[exact Output|exact FrameN|].
     intros pos;cbn [In] in OldD,OldW;repeat split;intuition congruence. }
   destruct (secp_write8s_layout mn bb 0 bd base bw edge cursor (schnorr_word_bytes ox) ltac:(lia)
    ltac:(rewrite schnorr_word_bytes_length;change (32<=18446744073709551615);lia)
    ltac:(clear -OldD;cbn [In] in OldD;intuition congruence)
    ltac:(clear -OldW;cbn [In] in OldW;intuition congruence) Buffer
    ltac:(rewrite schnorr_word_bytes_length;exact OutputN)) as (mf & Write & Effect).
   rewrite schnorr_word_bytes_length in Write,Effect.
   assert (ReadW:readonly_preserved mn mf) by (eapply secp_write8s_preserved;exact Write).
   assert (ReadyF:taptweak_ready mf) by (eapply taptweak_ready_after_write;[exact ReadyN|exact OutputN|exact ReadW|exact Effect]).
   pose proof (write_effect_lframe mn mf bd base bw edge cursor 256 (byte_sequence_cells (schnorr_word_bytes ox)) Effect) as FrameW.
   assert (Cells:byte_sequence_cells (schnorr_word_bytes ox)=Translate.encode ox).
   { unfold schnorr_word_bytes;rewrite byte_sequence_cells_encode,<-encode_vector_values;reflexivity. }
   destruct Effect as (OutCells & PrefixW & FieldsW & LoadsW & PermW & ValidW).
   assert (OwnedF:forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot.
     assert (Positive:0<hi).
     { clear -Slot;cbn [In] in Slot;destruct Slot as [Same|[Same|[Same|[Same|[]]]]];inversion Same;subst;lia. }
     eapply curve_keep_free;[exact Positive|apply OwnedN;exact Slot|exact FrameW|].
     intros pos;clear -Slot OldD OldW;cbn [In] in *;intuition congruence. }
   assert (Prefix:write_prefix_at m mf bw edge cursor).
   { eapply write_prefix_at_preserved with (mr:=mn) (me:=mf).
     - intros ofs w Load;rewrite (proj1 FrameN Mint64 bw ofs (load_valid _ _ _ _ _ Load));[exact Load|].
       intros pos Range;clear -OldW;cbn [In] in OldW;repeat split;intuition congruence.
     - intros;assumption.
     - exact PrefixW. }
   exists mf;rewrite Option;split.
   + rewrite taptweak_native_source,taptweak_write_source;eapply exec_statement_prefix_then_last;[exact Native|].
     eapply exec_taptweak_write_return;[exact WG|exact Buf|rewrite taptweak_native_destination;exact Dest|exact Write].
   + split.
     * unfold taptweak_output;rewrite Value;change (frame_output_cells_at mf bw edge cursor (Translate.encode ox) /\write_prefix_at m mf bw edge cursor /\frame_fields_at mf bd base bw edge (cursor-256)).
       split;[rewrite <-Cells;exact OutCells|];split;assumption.
     * split;[exact OwnedF|];split.
       -- eapply lframe_trans.
          { eapply lframe_implies;[exact FrameN|].
            intros b pos [Private [ND NW]] Valid;clear -Private;cbn [In] in Private;repeat split;intuition congruence. }
          eapply lframe_implies;[exact FrameW|intros b pos [Private [ND NW]] Valid;split;assumption].
       -- split.
          ++ intros chunk b ofs Valid Private OutsideD OutsideW;rewrite LoadsW by assumption.
             apply (proj1 FrameN);[exact Valid|intros;clear -Private;cbn [In] in Private;repeat split;intuition congruence].
          ++ split;[eapply mem_forward_trans;[exact ForwardN|exact (proj1 ReadW)]|exact ReadyF].
 - change (taptweak_result ng pk=Datatypes.false) in Option;rewrite Option in Native.
   exists mn;rewrite Option;split.
   + rewrite taptweak_native_source;eapply exec_statement_prefix_aborts;[discriminate|exact Native].
   + split;[unfold taptweak_output;rewrite Value;exact I|];split;[exact OwnedN|];split.
     * eapply lframe_implies;[exact FrameN|].
       intros b pos [Private [ND NW]] Valid;clear -Private;cbn [In] in Private;repeat split;intuition congruence.
     * split.
       -- intros chunk b ofs Valid Private OutsideD OutsideW;apply (proj1 FrameN);[exact Valid|].
          intros;clear -Private;cbn [In] in Private;repeat split;intuition congruence.
       -- split;[exact ForwardN|exact ReadyN].
Qed.

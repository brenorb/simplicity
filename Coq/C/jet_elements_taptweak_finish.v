(** Full actual native-to-frame-output suffix, including rejection. *)
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
Require Import C.jet_secp_curve_statements C.jet_secp_taptweak_finish C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_internal C.jet_clight_internal_frame.
Require Import C.jet_elements_taptweak_runtime_ready C.jet_elements_taptweak_runtime_write C.jet_elements_taptweak_parsed_native.
Lemma elements_taptweak_has_write8s:
 In(C.jets._write8s,C.jets.f_write8s)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)C.jets._write8s)elements_taptweak_curve_helpers=
 Some(C.jets._write8s,C.jets.f_write8s))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma exec_elements_taptweak_write_return e le m mf bb bd base:
 e!_write8s=None ->e!_buf=Some (bb,tarray tuchar 32) ->le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal C.jets.f_write8s)
 [Vptr bd (Ptrofs.repr base);Vptr bb Ptrofs.zero;Vlong (Int64.repr 32)] E0 mf Vundef ->
 Clight2.exec_stmt elements_taptweak_ge e le m taptweak_write_return E0 le mf (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros Global Buf Dest Write;unfold taptweak_write_return.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf);[|apply exec_Sreturn_some;constructor].
 destruct(elements_taptweak_curve_entries C.jets._write8s C.jets.f_write8s elements_taptweak_has_write8s) as (b0 & b & S0 & F0 & Symbol & Function).
 unfold taptweak_write,curve_call;eapply exec_Scall with (vf:=Vptr b Ptrofs.zero)
 (f:=Internal C.jets.f_write8s) (vargs:=[Vptr bd (Ptrofs.repr base);Vptr bb Ptrofs.zero;Vlong (Int64.repr 32)]) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   { eapply eval_Evar_global;[exact Global|exact Symbol]. }
   apply deref_loc_reference;reflexivity.
 - eapply eval_Econs;[apply eval_Etempvar;exact Dest|reflexivity|].
   eapply eval_Econs.
   { eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]. }
   { reflexivity. }
   eapply eval_Econs;[constructor|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Write.
Qed.
Local Opaque secp_ge Translate.encode canonical_fe_normalize taptweak_value taptweak_result.
Theorem exec_elements_taptweak_finish (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (ng pk:Ty.tySem (Word 8)) e le m bi bp bo bb bd base bw edge cursor:
 e!_input_pubkey=Some (bi,Tstruct __6478 noattr) ->e!_pubkey=Some (bp,Tstruct __2078 noattr) ->
 e!_output_pubkey=Some (bo,Tstruct __6478 noattr) ->e!_buf=Some (bb,tarray tuchar 32) ->
 e!_secp256k1_xonly_pubkey_tweak_add=None ->e!_secp256k1_xonly_pubkey_from_pubkey=None ->
 e!_secp256k1_xonly_pubkey_serialize=None ->e!_write8s=None ->le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 NoDup [bi;bp;bo;bb] ->~In bd [bi;bp;bo;bb] ->~In bw [bi;bp;bo;bb] ->
 (forall b hi,In (b,hi) [(bi,64);(bp,64);(bo,64);(bb,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 xonly_parse_result pk=Int.one ->xonly_parsed_result pk m bi ->elements_taptweak_runtime_ready m ->
 uint8_array_at m bb 0 (schnorr_word_bytes ng) ->write_frame_at m bd base bw edge cursor 256 ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m (root_drop_statements 11 (fn_body f_simplicity_generic_taptweak)) E0
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
 Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\mem_forward m mf /\elements_taptweak_runtime_ready mf /\readonly_preserved m mf.
Proof.
 intros KI KP KO Buf TG CG SG WG Dest Sep OldD OldW Owned Success Parsed Ready Bytes Output.
 destruct (exec_elements_taptweak_parsed_native Copy Clear Count ng pk e le m bi bp bo bb KI KP KO Buf TG CG SG
 Sep Owned Success Parsed Ready Bytes) as (mn & Native & Payload & OwnedN & FrameN & ForwardN & ReadyN & ReadN).
 pose proof (taptweak_result_option ng pk) as Option.
 destruct (taptweak_value ng pk) as [[x y]|] eqn:Value.
 - change (taptweak_result ng pk=Datatypes.true) in Option;rewrite Option in Native.
   pose (ox:=@canonical_fe_normalize Simplicity.Alg.CoreFunSem x).
   assert (Buffer:uint8_array_at mn bb 0 (schnorr_word_bytes ox)).
   { unfold taptweak_native_bytes in Payload;change (uint8_array_at mn bb 0 (map Int.repr (C.jet_secp_fe_b32.be_bytes (@toZ (WordToZ 8) ox)))) in Payload.
     rewrite word256_serializer_bytes in Payload;exact Payload. }
   assert (OutputN:write_frame_at mn bd base bw edge cursor 256).
   { eapply write_frame_at_framed;[exact Output|exact FrameN|].
     intros pos;clear -OldD OldW;cbn [In] in OldD,OldW;repeat split;intuition congruence. }
   destruct (secp_write8s_layout mn bb 0 bd base bw edge cursor (schnorr_word_bytes ox) ltac:(lia)
    ltac:(rewrite schnorr_word_bytes_length;change (32<=18446744073709551615);lia)
    ltac:(clear -OldD;cbn [In] in OldD;intuition congruence)
    ltac:(clear -OldW;cbn [In] in OldW;intuition congruence) Buffer
    ltac:(rewrite schnorr_word_bytes_length;exact OutputN)) as (mf & Write & Effect).
   rewrite schnorr_word_bytes_length in Write,Effect.
   pose proof(elements_taptweak_curve_transport _ _ mn _ E0 mf _ elements_taptweak_has_write8s Write)as WriteT.
   assert(ReadW:readonly_preserved mn mf)by(eapply elements_taptweak_internal_preserved;[exact elements_taptweak_has_write8s|exact WriteT]).
   assert (ReadyF:elements_taptweak_runtime_ready mf) by (eapply elements_taptweak_runtime_ready_after_write;[exact ReadyN|exact OutputN|exact ReadW|exact Effect]).
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
     eapply exec_elements_taptweak_write_return;[exact WG|exact Buf|rewrite taptweak_native_destination;exact Dest|exact WriteT].
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
          ++ split;[eapply mem_forward_trans;[exact ForwardN|exact(proj1 ReadW)]|];split;[exact ReadyF|eapply preserved_trans;[exact ReadN|exact ReadW]].
 - change (taptweak_result ng pk=Datatypes.false) in Option;rewrite Option in Native.
   exists mn;rewrite Option;split.
   + rewrite taptweak_native_source;eapply exec_statement_prefix_aborts;[discriminate|exact Native].
   + split;[unfold taptweak_output;rewrite Value;exact I|];split;[exact OwnedN|];split.
     * eapply lframe_implies;[exact FrameN|].
       intros b pos [Private [ND NW]] Valid;clear -Private;cbn [In] in Private;repeat split;intuition congruence.
     * split.
       -- intros chunk b ofs Valid Private OutsideD OutsideW;apply (proj1 FrameN);[exact Valid|].
          intros;clear -Private;cbn [In] in Private;repeat split;intuition congruence.
       -- split;[exact ForwardN|];split;[exact ReadyN|exact ReadN].
Qed.

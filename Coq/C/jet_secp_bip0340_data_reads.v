(** Actual message/signature reads of the public BIP340 wrapper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_word_repr C.jet_encoding C.jet_buffer_input C.jet_input_layout C.jet_frame_layout C.jet_frame_inv
 C.jet_read8s_layout C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_public_byte_read C.jet_secp_bip0340_public_entry C.jet_secp_bip0340_verifier_return
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb C.jet_secp_word_bytes_codec
 C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control C.jet_secp_schnorr_verify_parsed
 C.jet_secp_root_chain_owned C.jet_secp_statement_prefix C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Translate.encode.
Definition bip0340_read_bytes id n:=Scall None
 (Evar _read8s (Tfunction (Tcons (tptr tuchar) (Tcons tulong
  (Tcons (tptr (Tstruct _frameItem noattr)) Tnil))) tvoid cc_default))
 [Evar id (tarray tuchar n);Econst_int (Int.repr n) tint;
  Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition bip0340_data_read_statements:=[bip0340_read_bytes _msg 32;bip0340_read_bytes _sig 64].
Lemma bip0340_data_reads_source:root_drop_statements 3 (fn_body f_simplicity_bip_0340_verify)=
 statement_sequence bip0340_data_read_statements bip0340_verifier_return.
Proof. reflexivity. Qed.
Lemma exec_bip0340_read_bytes id n e le m mf bo bl:
 n=32 \/n=64 ->e!id=Some (bo,tarray tuchar n) ->e!_src=Some (bl,Tstruct _frameItem noattr) ->e!_read8s=None ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read8s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr n);Vptr bl Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (bip0340_read_bytes id n) E0 le mf Out_normal.
Proof.
 intros Size Buf Source Symbol Read.
 assert (Member:In (C.jets._read8s,C.jets.f_read8s) secp_core_helpers)
  by (unfold secp_core_helpers;do 19 right;left;reflexivity).
 destruct (secp_core_helpers_entries _ _ Member) as (b0 & bf & HS0 & HF0 & HS & HF).
 unfold bip0340_read_bytes;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
 (vargs:=[Vptr bo Ptrofs.zero;Vlong (Int64.repr n);Vptr bl Ptrofs.zero]) (f:=Internal C.jets.f_read8s) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Symbol|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|].
   eapply eval_Econs with (v1:=Vint (Int.repr n));[constructor|destruct Size as [Size|Size];subst n;reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Source|reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact Read.
Qed.
Theorem exec_bip0340_data_reads (pk msg r s:Ty.tySem (Word 8)) le m bl bb bkey bmsg bsig bi edge cursor:
 NoDup (bip0340_public_locals bl bb bkey bmsg bsig) ->bl<>bi ->bmsg<>bi ->bsig<>bi ->
 0<=cursor ->cursor+1024<=Int64.max_unsigned ->
 (forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 frame_fields_at m bl 0 bi edge (cursor+256) ->
 frame_input_cells_at m bi edge (cursor+256) (Translate.encode msg) ->
 frame_input_cells_at m bi edge (cursor+512) (@Translate.encode (Ty.Prod (Word 8) (Word 8)) (r,s)) ->
 xonly_parsed_result pk m bkey ->exists mf,
 Clight2.exec_stmt secp_ge (bip0340_public_env bl bb bkey bmsg bsig) le m
 (statement_sequence bip0340_data_read_statements Sskip) E0 le mf Out_normal /\
 schnorr_bytes_at mf bmsg Ptrofs.zero (schnorr_word_bytes msg) /\
 uint8_array_at mf bsig 0 (map Int.repr (xonly_input_bytes r)) /\
 uint8_array_at mf bsig 32 (map Int.repr (xonly_input_bytes s)) /\
 xonly_parsed_result pk mf bkey /\frame_fields_at mf bl 0 bi edge (cursor+1024) /\
 (forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bl /\b<>bmsg /\b<>bsig) m mf /\readonly_preserved m mf.
Proof.
 intros Separate LI MI SI Cursor Max Owned Source MsgInput SigInput Parsed.
 assert (Pairs:bmsg<>bl /\bsig<>bl /\bmsg<>bsig /\bkey<>bl /\bkey<>bmsg /\bkey<>bsig).
 { clear -Separate;unfold bip0340_public_locals in Separate;repeat rewrite NoDup_cons_iff in *;
   cbn [In] in *;intuition congruence. }
 destruct Pairs as (ML & SL & MS & KL & KM & KS).
 pose (xs:=vector_values (Word 3) 5 msg).
 assert (LX:length xs=32%nat) by (unfold xs;apply vector_values_length).
 assert (InputM:frame_input_cells_at m bi edge (cursor+256) (concat (map (@Translate.encode (Word 3)) xs))).
 { unfold xs;rewrite <-(encode_vector_values (Word 3) 5 msg);exact MsgInput. }
 destruct (eval_secp_public_byte_read xs m bmsg bl bi edge (cursor+256)
  ltac:(rewrite LX;clear;change (32<=18446744073709551615);lia) ltac:(lia) ltac:(rewrite LX;lia) ML LI MI
  ltac:(rewrite LX;apply Owned;clear;cbn [bip0340_public_storage In];tauto)
  (Owned bl 16 ltac:(clear;cbn [bip0340_public_storage In];tauto)) Source InputM)
 as (mm & MsgRead & MsgBytes & FieldsM & KeepM & FrameM & ReadM).
 pose (ys:=vector_values (Word 3) 6 (r,s)).
 assert (LY:length ys=64%nat) by (unfold ys;apply vector_values_length).
 assert (FieldsS:frame_fields_at mm bl 0 bi edge (cursor+512)).
 { rewrite LX in FieldsM;replace (cursor+256+8*Z.of_nat 32) with (cursor+512) in FieldsM by lia;exact FieldsM. }
 assert (InputS:frame_input_cells_at mm bi edge (cursor+512) (concat (map (@Translate.encode (Word 3)) ys))).
 { eapply buffer_input_cells_preserved.
   - intros ofs w Load;rewrite (proj1 FrameM Mint64 bi ofs (load_valid _ _ _ _ _ Load));
     [exact Load|intros;split;congruence].
   - unfold ys;rewrite <-(encode_vector_values (Word 3) 6 (r,s));exact SigInput. }
 destruct (eval_secp_public_byte_read ys mm bsig bl bi edge (cursor+512)
  ltac:(rewrite LY;clear;change (64<=18446744073709551615);lia) ltac:(lia) ltac:(rewrite LY;lia) SL LI SI
  ltac:(rewrite LY;intros pos Range;apply KeepM;apply (Owned bsig 64);[clear;cbn [bip0340_public_storage In];tauto|exact Range])
  ltac:(intros pos Range;apply KeepM;apply (Owned bl 16);[clear;cbn [bip0340_public_storage In];tauto|exact Range]) FieldsS InputS)
 as (mf & SigRead & SigBytes & FieldsF & KeepS & FrameS & ReadS).
 assert (MsgBytesF:uint8_array_at mf bmsg 0 (schnorr_word_bytes msg)).
 { eapply uint8_array_framed;[exact MsgBytes|exact FrameS|intros;split;assumption]. }
 change (uint8_array_at mf bsig 0 (map word8_array_value
  (vector_values (Word 3) 5 r++vector_values (Word 3) 5 s))) in SigBytes.
 rewrite map_app in SigBytes;change (uint8_array_at mf bsig 0 (schnorr_word_bytes r++schnorr_word_bytes s)) in SigBytes.
 destruct (uint8_array_split_app mf bsig 0 _ _ SigBytes) as [RBytes SBytes].
 rewrite schnorr_word_bytes_length in SBytes;change (uint8_array_at mf bsig 32 (schnorr_word_bytes s)) in SBytes.
 assert (Frame:lframe (fun b _=>b<>bl /\b<>bmsg /\b<>bsig) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameM|];intros b pos (NL & NM & _) _;split;assumption.
   - eapply lframe_implies;[exact FrameS|];intros b pos (NL & _ & NS) _;split;assumption. }
 exists mf;split.
 - cbn [bip0340_data_read_statements statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mm) (le1:=le).
   + eapply exec_bip0340_read_bytes with (bo:=bmsg) (bl:=bl);try reflexivity;[left;reflexivity|rewrite LX in MsgRead;exact MsgRead].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le);[|constructor].
     eapply exec_bip0340_read_bytes with (bo:=bsig) (bl:=bl);try reflexivity;[right;reflexivity|rewrite LY in SigRead;exact SigRead].
 - split.
   + intros i Index;apply MsgBytesF;apply nth_error_nth';exact Index.
   + split;[unfold xonly_input_bytes;rewrite word256_serializer_bytes;exact RBytes|].
     split;[unfold xonly_input_bytes;rewrite word256_serializer_bytes;exact SBytes|].
     split.
     * eapply xonly_parsed_result_framed;[exact Parsed|exact Frame|intros;repeat split;assumption].
     * split.
       -- rewrite LY in FieldsF;replace (cursor+512+8*Z.of_nat 64) with (cursor+1024) in FieldsF by lia;exact FieldsF.
       -- split;[intros b hi Slot pos Range;apply KeepS,KeepM;exact (Owned b hi Slot pos Range)|].
          split;[exact Frame|eapply preserved_trans;[exact ReadM|exact ReadS]].
Qed.

(** Shared original 64-byte read for CheckSig's message and signature. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate
 C.jet_word_repr C.jet_encoding C.jet_buffer_input C.jet_input_layout C.jet_frame_layout
 C.jet_read8s_layout C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_public_byte_read C.jet_secp_bip0340_data_reads C.jet_secp_schnorr_challenge_hash
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Translate.encode.
Theorem exec_secp_public_pair_read (a b:Ty.tySem (Word 8)) id e le m bo bf bi edge cursor:
 e!id=Some (bo,tarray tuchar 64) ->e!_src=Some (bf,Tstruct _frameItem noattr) ->e!_read8s=None ->
 0<=cursor ->cursor+512<=Int64.max_unsigned ->bo<>bf ->bf<>bi ->bo<>bi ->
 Mem.range_perm m bo 0 64 Cur Freeable ->Mem.range_perm m bf 0 16 Cur Freeable ->
 frame_fields_at m bf 0 bi edge cursor ->
 frame_input_cells_at m bi edge cursor (@Translate.encode (Word 9) (a,b)) ->exists mf,
 Clight2.exec_stmt secp_ge e le m (bip0340_read_bytes id 64) E0 le mf Out_normal /\
 uint8_array_at mf bo 0 (schnorr_word_bytes a++schnorr_word_bytes b) /\
 frame_fields_at mf bf 0 bi edge (cursor+512) /\
 keeps_permissions m mf /\lframe (fun block _=>block<>bf /\block<>bo) m mf /\readonly_preserved m mf.
Proof.
 intros Buf Frame Symbol Cursor Max OF FI OI FO FF Fields Input.
 pose (xs:=vector_values (Word 3) 6 (a,b)).
 assert (Length:length xs=64%nat) by (unfold xs;apply vector_values_length).
 assert (InputBytes:frame_input_cells_at m bi edge cursor (concat (map (@Translate.encode (Word 3)) xs))).
 { unfold xs;rewrite <-(encode_vector_values (Word 3) 6 (a,b));exact Input. }
 destruct (eval_secp_public_byte_read xs m bo bf bi edge cursor
  ltac:(rewrite Length;clear;change (64<=18446744073709551615);lia) Cursor
  ltac:(rewrite Length;exact Max) OF FI OI ltac:(rewrite Length;exact FO) FF Fields InputBytes)
 as (mf & Read & Bytes & FieldsF & Keep & FrameF & Readonly).
 rewrite Length in Read,FieldsF.
 exists mf;split.
 - eapply exec_bip0340_read_bytes;[right;reflexivity|exact Buf|exact Frame|exact Symbol|exact Read].
 - split.
   + change (uint8_array_at mf bo 0 (map word8_array_value
     (vector_values (Word 3) 5 a++vector_values (Word 3) 5 b))) in Bytes.
     rewrite map_app in Bytes;exact Bytes.
   + split;[exact FieldsF|];split;[exact Keep|];split;[exact FrameF|exact Readonly].
Qed.

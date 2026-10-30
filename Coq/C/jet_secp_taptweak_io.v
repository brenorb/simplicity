(** Exact original TapTweak key reader and output writer/return boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_bitcoin_effects C.jet_output_layout C.jet_output_sequence_step C.jet_frame_layout C.jet_encoding C.jet_word_repr C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_frame
 C.jet_read8s_layout C.jet_buffer_input C.jet_write8s_layout C.jet_write8_sequence C.jet_write_layout
 C.jet_secp_curve_statements C.jet_secp_root_chain_owned C.jet_secp_schnorr_challenge_hash.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_key_read:=curve_call _read8s C.jets.f_read8s None
 [Evar _buf (tarray tuchar 32);Econst_int (Int.repr 32) tint;Etempvar _src (tptr (Tstruct _frameItem noattr))].
Definition taptweak_write:=curve_call _write8s C.jets.f_write8s None
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));Evar _buf (tarray tuchar 32);Econst_int (Int.repr 32) tint].
Definition taptweak_write_return:=Ssequence taptweak_write (Sreturn (Some (Econst_int Int.one tint))).
Lemma taptweak_key_read_source:root_drop_statements 4 (fn_body f_simplicity_generic_taptweak)=
 Ssequence taptweak_key_read (root_drop_statements 5 (fn_body f_simplicity_generic_taptweak)).
Proof. reflexivity. Qed.
Lemma taptweak_write_source:root_drop_statements 14 (fn_body f_simplicity_generic_taptweak)=taptweak_write_return.
Proof. reflexivity. Qed.
Local Opaque secp_ge Translate.encode.
Lemma exec_taptweak_key_read e le m mf bb bf:
 e!_read8s=None ->e!_buf=Some (bb,tarray tuchar 32) ->le!_src=Some (Vptr bf Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read8s)
 [Vptr bb Ptrofs.zero;Vlong (Int64.repr 32);Vptr bf Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m taptweak_key_read E0 le mf Out_normal.
Proof.
 intros Global Buf Source Read.
 destruct (secp_core_helpers_entries C.jets._read8s C.jets.f_read8s
 ltac:(unfold secp_core_helpers;do 19 right;left;reflexivity)) as (b0 & b & S0 & F0 & Symbol & Function).
 unfold taptweak_key_read,curve_call;eapply exec_Scall with (vf:=Vptr b Ptrofs.zero)
 (f:=Internal C.jets.f_read8s) (vargs:=[Vptr bb Ptrofs.zero;Vlong (Int64.repr 32);Vptr bf Ptrofs.zero]) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   { eapply eval_Evar_global;[exact Global|exact Symbol]. }
   apply deref_loc_reference;reflexivity.
 - eapply eval_Econs.
   { eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]. }
   { reflexivity. }
   eapply eval_Econs;[constructor|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact Source|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Read.
Qed.
Lemma exec_taptweak_write_return e le m mf bb bd base:
 e!_write8s=None ->e!_buf=Some (bb,tarray tuchar 32) ->le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_write8s)
 [Vptr bd (Ptrofs.repr base);Vptr bb Ptrofs.zero;Vlong (Int64.repr 32)] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m taptweak_write_return E0 le mf (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros Global Buf Dest Write;unfold taptweak_write_return.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf);[|apply exec_Sreturn_some;constructor].
 destruct (secp_core_helpers_entries C.jets._write8s C.jets.f_write8s
 ltac:(unfold secp_core_helpers;do 18 right;left;reflexivity)) as (b0 & b & S0 & F0 & Symbol & Function).
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
Theorem eval_taptweak_write_return (x:Ty.tySem (Word 8)) e le m bb bd base bw edge cursor:
 e!_write8s=None ->e!_buf=Some (bb,tarray tuchar 32) ->le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 bb<>bd ->bb<>bw ->uint8_array_at m bb 0 (schnorr_word_bytes x) ->
 write_frame_at m bd base bw edge cursor 256 ->exists mf,
 Clight2.exec_stmt secp_ge e le m taptweak_write_return E0 le mf (Out_return (Some (Vint Int.one,tint))) /\
 write_effect m mf bd base bw edge cursor 256 (Translate.encode x).
Proof.
 intros Global Buf Dest BD BW Bytes Frame.
 destruct (secp_write8s_layout m bb 0 bd base bw edge cursor (schnorr_word_bytes x)
 ltac:(lia) ltac:(rewrite schnorr_word_bytes_length;change (32<=18446744073709551615);lia)
 BD BW Bytes ltac:(rewrite schnorr_word_bytes_length;exact Frame)) as (mf & Write & Effect).
 rewrite schnorr_word_bytes_length in Write,Effect.
 assert (Cells:byte_sequence_cells (schnorr_word_bytes x)=Translate.encode x).
 { unfold schnorr_word_bytes;rewrite byte_sequence_cells_encode,<-encode_vector_values;reflexivity. }
 rewrite Cells in Effect;exists mf;split;[eapply exec_taptweak_write_return;[exact Global|exact Buf|exact Dest|exact Write]|exact Effect].
Qed.

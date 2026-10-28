(** Complete initialized local C-to-literal-Simplicity scale contract.
    Registration and canonical-source binding are separately audited. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_clight_internal_preserve C.jet_secp_strauss_zero_generator C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding
 C.jet_secp_frame C.jet_secp_scale_startup C.jet_secp_strauss_complete_program.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_memset_model C.jet_secp_scale_lifecycle.
Require Import Simplicity.Translate.
Require Import C.jet_word_repr C.jet_write_layout C.jet_secp_initialized_contract.
Require Import C.jet_secp_scalar_table_literal.
Require Import C.jet_secp_checked_scale_startup C.jet_secp_checked_scale_lifecycle
 C.jet_secp_checked_scale_literal C.jet_secp_initialized_partial_contract C.jet_partial
 C.jet_secp_curve_literal Simplicity.Util.Option.
Require Import C.jet_readBit_layout.
Local Opaque literal_checked_scale Simplicity.Translate.encode.
Theorem checked_scale_initialized_local_spec :
 memset_model -> secp_jet_initialized_partial_local_spec checked_scale_startup f_simplicity_scale
 (Ty.Prod (Word 8) literal_table_gej) literal_table_gej
 (@literal_checked_scale (Alg.AssertionSem option_Monad_Zero)).
Proof.
 intros Model env m bd base bs sbase bi bw edge outedge cursor rc value
  Ready Base Align Source RC Max Input Output.
 destruct value as [raw [[ax ay] az]].
 change (rc+1024<=Int64.max_unsigned) in Max.
 change (write_frame_at m bd base bw outedge cursor 768) in Output.
 change (frame_input_cells_at m bi edge rc (encode raw++((encode ax++encode ay)++encode az))) in Input.
 rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in Input.
 destruct Input as [Raw [[AX AY] AZ]].
 change (frame_input_cells_at m bi edge (rc+256) (encode ax)) in AX.
 change (frame_input_cells_at m bi edge (rc+256+256) (encode ay)) in AY.
 replace (rc+256+256) with (rc+512) in AY by lia.
 change (frame_input_cells_at m bi edge (rc+256+512) (encode az)) in AZ.
 replace (rc+256+512) with (rc+768) in AZ by lia.
 rewrite encode_word in Raw,AX,AY,AZ.
 destruct (eval_checked_scale_initialized Model env m bd base bs sbase bw outedge cursor 768 bi edge rc
  raw ax ay az Ready Output ltac:(clear;lia) Base Align Source Raw AX AY AZ RC Max)
  as (mf & Call & Final & Frame & ReadyF).
 pose (result:=if Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((ax,ay),az))
  then Some (@literal_off_curve_scale Alg.CoreFunSem (raw,((ax,ay),az))) else None).
 assert (Return:Vint (bit_int (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((ax,ay),az))))=
  jet_partial_return result).
 { unfold result;destruct (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((ax,ay),az)));reflexivity. }
 assert (FinalResult:finv m bd base bw outedge cursor 768 bi mf
  (match result with Some _=>true|None=>false end)
  (match result with Some value=>encode value|None=>[] end)).
 { unfold result;destruct (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((ax,ay),az)));exact Final. }
 destruct (partial_frame_observations literal_table_gej m bd base bw outedge cursor 768 bi mf
  result FinalResult Frame) as (Observations & Footprint).
 rewrite Return in Call.
 exists mf;rewrite literal_checked_scale_option.
 fold result.
 split;[exact Call|];split;[exact Observations|];split;[exact Footprint|exact ReadyF].
Qed.


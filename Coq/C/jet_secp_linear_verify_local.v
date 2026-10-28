(** Public implementation-to-Simplicity assertion contract for linear_verify_1. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_readBit_layout C.jet_sx_mem
 C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_frame C.jet_write_layout C.jet_word_repr C.jet_partial
 C.jet_secp_initialized_partial_contract C.jet_secp_linear_startup C.jet_memset_model
 C.jet_secp_linear_verify_literal C.jet_secp_linear_verify_lifecycle.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_linear_check Simplicity.Translate.encode.

Theorem linear_verify_initialized_local_spec :
 memset_model -> secp_jet_initialized_partial_local_spec linear_startup f_simplicity_linear_verify_1
 literal_linear_verify_args Ty.Unit
 (@literal_linear_verify (Alg.AssertionSem option_Monad_Zero)).
Proof.
 intros Model env m bd base bs sbase bi bw edge outedge cursor rc value
  Ready Base Align Source RC Max Input Output.
 destruct value as [[[raw [ax ay]] ng] [bxword byword]].
 change (rc+1536<=Int64.max_unsigned) in Max.
 change (write_frame_at m bd base bw outedge cursor 0) in Output.
 change (frame_input_cells_at m bi edge rc
   (((encode raw++(encode ax++encode ay))++encode ng)++(encode bxword++encode byword))) in Input.
 rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in Input.
 destruct Input as [[[Raw [AX AY]] NG] [BX BY]].
 change (frame_input_cells_at m bi edge (rc+256) (encode ax)) in AX.
 change (frame_input_cells_at m bi edge (rc+256+256) (encode ay)) in AY.
 replace (rc+256+256) with (rc+512) in AY by lia.
 change (frame_input_cells_at m bi edge (rc+768) (encode ng)) in NG.
 change (frame_input_cells_at m bi edge (rc+1024) (encode bxword)) in BX.
 change (frame_input_cells_at m bi edge (rc+1024+256) (encode byword)) in BY.
 replace (rc+1024+256) with (rc+1280) in BY by lia.
 rewrite encode_word in Raw,AX,AY,NG,BX,BY.
 destruct (eval_linear_verify_initialized Model env m bd base bs sbase bw outedge cursor 0 bi edge rc
  raw ng ax ay bxword byword Ready Output Base Align Source Raw AX AY NG BX BY RC Max)
  as (mf & Call & Final & Frame & ReadyF).
 pose (result:=if Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword)))
  then Some tt else None).
 assert (Return:Vint (bit_int (Bit.toBool
   (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword)))))=jet_partial_return result).
 { unfold result;destruct (Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword))));reflexivity. }
 assert (FinalResult:finv m bd base bw outedge cursor 0 bi mf
  (match result with Some _=>true|None=>false end)
  (match result with Some value=>@encode Ty.Unit value|None=>[] end)).
 { unfold result;destruct (Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword))));exact Final. }
 destruct (partial_frame_observations Ty.Unit m bd base bw outedge cursor 0 bi mf result FinalResult Frame)
  as (Observations & Footprint).
 rewrite Return in Call.
 exists mf;rewrite literal_linear_verify_option;fold result.
 split;[exact Call|];split;[exact Observations|];split;[exact Footprint|exact ReadyF].
Qed.

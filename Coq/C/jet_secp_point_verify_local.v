(** Public implementation-to-Simplicity assertion contract for point_verify_1. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_readBit_layout C.jet_sx_mem
 C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_frame C.jet_write_layout C.jet_word_repr C.jet_partial
 C.jet_secp_initialized_partial_contract C.jet_secp_linear_startup C.jet_memset_model
 C.jet_secp_point_verify_literal C.jet_secp_point_verify_lifecycle.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_point_check Simplicity.Translate.encode.

Theorem point_verify_initialized_local_spec :
 memset_model -> secp_jet_initialized_partial_local_spec linear_startup f_simplicity_point_verify_1
 literal_point_verify_args Ty.Unit
 (@literal_point_verify (Alg.AssertionSem option_Monad_Zero)).
Proof.
 intros Model env m bd base bs sbase bi bw edge outedge cursor rc value
  Ready Base Align Source RC Max Input Output.
 destruct value as [[[raw [ay ax]] ng] [bybit bxword]].
 change (rc+1026<=Int64.max_unsigned) in Max.
 change (write_frame_at m bd base bw outedge cursor 0) in Output.
 change (frame_input_cells_at m bi edge rc
   (((encode raw++@encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (ay,ax))++encode ng)++
     @encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (bybit,bxword))) in Input.
 rewrite !frame_input_cells_at_app,!app_length,!encode_length in Input.
 destruct Input as [[[Raw AX] NG] BX].
 change (frame_input_cells_at m bi edge (rc+256) (@encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (ay,ax))) in AX.
 change (frame_input_cells_at m bi edge (rc+513) (encode ng)) in NG.
 change (frame_input_cells_at m bi edge (rc+769) (@encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (bybit,bxword))) in BX.
 rewrite encode_word in Raw,NG.
 destruct (eval_point_verify_initialized Model env m bd base bs sbase bw outedge cursor 0 bi edge rc
  raw ng ax bxword ay bybit Ready Output Base Align Source Raw AX NG BX RC Max)
  as (mf & Call & Final & Frame & ReadyF).
 pose (result:=if Bit.toBool (@literal_point_check Alg.CoreFunSem (((raw,(ay,ax)),ng),(bybit,bxword)))
  then Some tt else None).
 assert (Return:Vint (bit_int (Bit.toBool
   (@literal_point_check Alg.CoreFunSem (((raw,(ay,ax)),ng),(bybit,bxword)))))=jet_partial_return result).
 { unfold result;destruct (Bit.toBool (@literal_point_check Alg.CoreFunSem (((raw,(ay,ax)),ng),(bybit,bxword))));reflexivity. }
 assert (FinalResult:finv m bd base bw outedge cursor 0 bi mf
  (match result with Some _=>true|None=>false end)
  (match result with Some value=>@encode Ty.Unit value|None=>[] end)).
 { unfold result;destruct (Bit.toBool (@literal_point_check Alg.CoreFunSem (((raw,(ay,ax)),ng),(bybit,bxword))));exact Final. }
 destruct (partial_frame_observations Ty.Unit m bd base bw outedge cursor 0 bi mf result FinalResult Frame)
  as (Observations & Footprint).
 rewrite Return in Call.
 exists mf;rewrite literal_point_verify_option;fold result.
 split;[exact Call|];split;[exact Observations|];split;[exact Footprint|exact ReadyF].
Qed.

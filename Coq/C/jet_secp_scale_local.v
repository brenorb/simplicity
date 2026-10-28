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
Theorem off_curve_scale_initialized_local_spec :
 memset_model -> secp_jet_initialized_local_spec scale_startup f_simplicity_off_curve_scale
 (Ty.Prod (Word 8) literal_table_gej) literal_table_gej (@literal_off_curve_scale Alg.CoreFunSem).
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
 destruct (eval_off_curve_scale_initialized Model env m bd base bs sbase bw outedge cursor 768 bi edge rc
  raw ax ay az Ready Output ltac:(clear;lia) Base Align Source Raw AX AY AZ RC Max)
  as (mf & Call & Final & Frame & ReadyF).
 destruct Final as (Valid & FinFrame & Cap & (Cells & Prefix & Fields & Loads & Perms) & Written).
 rewrite encode_length in Fields,Loads.
 exists mf;split;[exact Call|];split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|];split;[|exact ReadyF].
 intros chunk b ofs V FrameOther OutputOther.
 destruct (Pos.eq_dec b bd) as [D|D];
  [apply Loads;[split;[left;exact D|exact V]|exact FrameOther|exact OutputOther]|].
 destruct (Pos.eq_dec b bw) as [W|W];
  [apply Loads;[split;[right;left;exact W|exact V]|exact FrameOther|exact OutputOther]|].
 destruct (Pos.eq_dec b bi) as [I|I];
  [apply Loads;[split;[right;right;exact I|exact V]|exact FrameOther|exact OutputOther]|].
 apply (proj1 Frame);[exact V|].
 intros pos Range;unfold extA,fext;intros [[Same|[Same|Same]] _];contradiction.
Qed.

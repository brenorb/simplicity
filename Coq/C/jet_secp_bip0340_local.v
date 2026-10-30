(** Public initialized implementation-to-frozen-Simplicity BIP340 assertion contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_readBit_layout C.jet_sx_mem
 C.jet_frame_spec C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_frame C.jet_write_layout C.jet_word_repr C.jet_partial C.jet_secp_initialized_partial_contract
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_secp_schnorr_startup
 C.jet_secp_schnorr_challenge_literal C.jet_secp_schnorr_verify_literal C.jet_secp_bip0340_function.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_bip0340_check Simplicity.Translate.encode.
Theorem bip0340_initialized_local_spec :
 memcpy_model ->memset_model ->ctz_model ->
 secp_jet_initialized_partial_local_spec schnorr_startup f_simplicity_bip_0340_verify
 literal_bip0340_args Ty.Unit (@literal_bip0340_verify (Alg.AssertionSem option_Monad_Zero)).
Proof.
 intros Copy Clear Count env m bd base bs sbase bi bw edge outedge cursor rc value
  Ready Base Align Source RC Max Input Output.
 destruct value as [[pk msg] [r s]].
 change (rc+1024<=Int64.max_unsigned) in Max.
 change (write_frame_at m bd base bw outedge cursor 0) in Output.
 change (frame_input_cells_at m bi edge rc ((encode pk++encode msg)++@encode (Ty.Prod (Word 8) (Word 8)) (r,s))) in Input.
 rewrite frame_input_cells_at_app in Input;destruct Input as [KeyMsg Sig].
 rewrite app_length,!encode_length in Sig.
 change (frame_input_cells_at m bi edge (rc+512) (@encode (Ty.Prod (Word 8) (Word 8)) (r,s))) in Sig.
 rewrite frame_input_cells_at_app in KeyMsg;destruct KeyMsg as [Key Msg].
 rewrite encode_length in Msg.
 change (frame_input_cells_at m bi edge (rc+256) (encode msg)) in Msg.
 destruct (eval_bip0340_public Copy Clear Count pk msg r s env m bd base bs sbase bi edge rc
  Ready Base Align Source Key Msg Sig RC Max) as (mf & Call & Frame & Forward & ReadyF).
 pose (result:=if Simplicity.Bit.toBool (@literal_bip0340_check Alg.CoreFunSem ((pk,msg),(r,s))) then Some tt else None).
 assert (Return:Vint (bit_int (Simplicity.Bit.toBool (@literal_bip0340_check Alg.CoreFunSem ((pk,msg),(r,s)))))=jet_partial_return result).
 { unfold result;destruct (Simplicity.Bit.toBool (@literal_bip0340_check Alg.CoreFunSem ((pk,msg),(r,s))));reflexivity. }
 rewrite Return in Call.
 exists mf;rewrite literal_bip0340_verify_option;fold result.
 split;[exact Call|];split.
 - change (match result with Some value=>frame_output_cells_at mf bw outedge cursor (@encode Ty.Unit value) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor-Z.of_nat (bitSize Ty.Unit))|None=>True end).
   destruct result as [value|];[destruct value|exact I].
   change (frame_output_cells_at mf bw outedge cursor [] /\write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor-0)).
   split;[intros i c Nth;destruct i;discriminate Nth|];split.
   + intros old Load;exists old;split.
     * rewrite (proj1 Frame Mint64 bw (write_word_address outedge cursor) (load_valid _ _ _ _ _ Load));[exact Load|intros;exact I].
     * unfold word_outside_eq;intros;reflexivity.
   + replace (cursor-0) with cursor by lia;destruct (proj1 (proj2 Output)) as [Edge Cursor].
     split.
     * rewrite (proj1 Frame Mptr bd base (load_valid _ _ _ _ _ Edge));[exact Edge|intros;exact I].
     * rewrite (proj1 Frame Mint64 bd (base+8) (load_valid _ _ _ _ _ Cursor));[exact Cursor|intros;exact I].
 - split;[intros chunk b ofs Valid _ _;apply (proj1 Frame);[exact Valid|intros;exact I]|exact ReadyF].
Qed.

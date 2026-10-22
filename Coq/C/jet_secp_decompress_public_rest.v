(** All public decompression calls discharged from general frames and owners. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Bit Simplicity.Alg Simplicity.Translate.
Require Import C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_decompress_public_entry C.jet_secp_decompress_public_body C.jet_secp_decompress_reads
 C.jet_secp_decompress_helper_literal C.jet_secp_decompress_result_write C.jet_secp_decompress_output
 C.jet_secp_decompress_literal C.jet_secp_root_function_literal C.jet_secp_root_check
 C.jet_secp_decompress_numeric C.jet_secp_rescale_public_reads C.jet_secp_curve_frame
 C.jet_secp_square_spec_bridge C.jet_secp_multiply_normalize_bridge.
Require C.jets.
Import ListNotations.
Local Notation Bit := (Ty.Sum Ty.Unit Ty.Unit).
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress Simplicity.Translate.encode square_reader_rho
 root_check_flag decompress_root_words.

Theorem exec_decompress_public_rest_owned le m0 bd base bw outedge cursor N bi edge rc
 (odd : Ty.tySem Bit) (x : Ty.tySem (Word 8)) m bx br bl :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 write_frame_at m0 bd base bw outedge cursor N -> 513<=N ->
 frame_input_cells_at m0 bi edge rc (@Simplicity.Translate.encode (Ty.Prod Bit (Word 8)) (odd,x)) ->
 0<=rc -> rc+257<=Int64.max_unsigned ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
 bx<>bl -> br<>bl -> bx<>br -> xsep (extA m0 bd bw bi) [(bx,0);(br,0);(bl,0)] ->
 finv m0 bd base bw outedge cursor N bi m false [] -> exists mf,
 Clight2.exec_stmt secp_ge (decompress_public_env bl bx br) le m decompress_public_rest E0
  (decompress_final_temps le (Bit.toBool odd) (root_check_flag (decompress_root_words (square_reader_rho x))))
  mf (Out_return (Some (Vint Int.one,tint))) /\
 finv m0 bd base bw outedge cursor N bi mf true
  (Simplicity.Translate.encode (@literal_decompress Simplicity.Alg.CoreFunSem (odd,x))) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\
 lframe (rescale_locals_outside m0 bd bw bi bx br bl) m mf.
Proof.
 intros HD Output Cap Input RC Max XF RF LF Source XL RL XR Sep Inv.
 assert (OutX : ~extA m0 bd bw bi bx) by exact (Sep 0%nat ltac:(cbn;lia)).
 assert (OutR : ~extA m0 bd bw bi br) by exact (Sep 1%nat ltac:(cbn;lia)).
 assert (OutL : ~extA m0 bd bw bi bl) by exact (Sep 2%nat ltac:(cbn;lia)).
 destruct (eval_decompress_readers m0 bd base bw outedge cursor N bi edge rc odd x m bx br bl
   Output Cap Input RC Max XF RF LF Source XL RL XR Sep Inv)
   as (mp & mr & Parity & Read & Field & XFR & RFR & LFR & InvR & FrameR).
 destruct (eval_decompress_helper_literal (square_reader_rho x) x odd mr bx br XR
   (root_reader_matches x) Field XFR RFR)
   as (mn & Helper & X & Y & BoundX & BoundY & Finite & Machine & XFN & RFN & FrameN).
 assert (InvN : finv m0 bd base bw outedge cursor N bi mn false []).
 { eapply finv_stable;[exact Output|exact InvR|].
   eapply lframe_implies;[exact FrameN|];intros b pos HE VB;split;intro EQ;subst b;contradiction. }
 assert (LFN : Mem.range_perm mn bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact LFR|exact FrameN|];intros;split;congruence. }
 set (bit := root_check_flag (decompress_root_words (square_reader_rho x))).
 rewrite <-Machine in Helper.
 assert (TagValue : (match decompress_machine_result (square_reader_rho x) (Bit.toBool odd)
   with inl _=>Int.zero | inr _=>Int.one end)=(if bit then Int.one else Int.zero)).
 { unfold decompress_machine_result,bit;
   destruct (root_check_flag (decompress_root_words (square_reader_rho x)));reflexivity. }
 rewrite TagValue in Helper.
 destruct (eval_decompress_result_writes m0 bd base bw outedge cursor N bi rc mn br
   (decompress_input_field (square_reader_rho x))
   (decompress_y_field (square_reader_rho x) (Bit.toBool odd)) bit
   Output Cap InvN BoundX BoundY X Y RFN OutR)
   as (mt & mf & Tag & Payload & Final & RFF & FrameW).
 assert (XFF : Mem.range_perm mf bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact XFN|exact FrameW|];intros;split;congruence. }
 assert (LFF : Mem.range_perm mf bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact LFN|exact FrameW|];intros;split;congruence. }
 change (finv m0 bd base bw outedge cursor N bi mf true
   (Simplicity.Translate.encode (decompress_machine_result (square_reader_rho x) (Bit.toBool odd)))) in Final.
 rewrite Machine in Final.
 exists mf;split.
 - eapply exec_decompress_public_rest_from_calls;eassumption.
 - split;[exact Final|];split;[exact XFF|];split;[exact RFF|];split;[exact LFF|].
   eapply lframe_trans;[exact FrameR|];eapply lframe_trans.
   + eapply lframe_implies;[exact FrameN|];intros b pos (NX & NR & NL & NE) VB;split;assumption.
   + eapply lframe_implies;[exact FrameW|];intros b pos (NX & NR & NL & NE) VB;split;assumption.
Qed.

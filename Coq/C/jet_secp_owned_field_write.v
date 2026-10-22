(** Original bounded field writer after any established output prefix. This
    supports conditional payloads without resetting cursors or output bits. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_rep
 C.jet_frame_inv C.jet_output_layout C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_writer_bridge
 C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec C.jet_secp_square_columns C.jet_secp_rescale_literal.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output Simplicity.Translate.encode.

Theorem eval_owned_field_write m0 bd base bw edge cursor N bi written0 outs0 m br w :
 write_frame_at m0 bd base bw edge cursor N -> Z.of_nat (length outs0)+256<=N ->
 square_input_bounds w -> fe_at m br 0 (words5 w) -> Mem.range_perm m br 0 40 Cur Freeable ->
 ~extA m0 bd bw bi br -> finv m0 bd base bw edge cursor N bi m written0 outs0 -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_write_fe)
   (Vptr bd (Ptrofs.repr base)::Vptr br Ptrofs.zero::nil) E0 mf Vundef /\
 finv m0 bd base bw edge cursor N bi mf true (outs0++encode (rescale_field_output w)) /\
 Mem.range_perm mf br 0 40 Cur Freeable /\
 lframe (fun b _=>b<>br /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Cap Bound Field Free Outside Inv.
 set (rho:=wide_fe_rho (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat) 0).
 assert (Rep : rep rho [(br,0)] local_write_initial_regs m).
 { apply wide_initial_from_owned_words;[exact Field|exact Free]. }
 assert (Sep : xsep (extA m0 bd bw bi) [(br,0)]).
 { intros [|r] HR;[exact Outside|cbn in HR;lia]. }
 assert (FrameInv : invA m0 bd base bw edge cursor N bi 0 written0 outs0 256 rho [] m).
 { unfold invA;split;[reflexivity|].
   cbn [has_wr outsA written];rewrite app_nil_r,Bool.orb_false_r;split;[exact Inv|];split;[exact Cap|lia]. }
 pose proof (rescale_writer_bounds w Bound) as Bounds.
 destruct (eval_local_wide_write_fe m0 bd base bw edge cursor N bi 0
   (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat) written0 outs0 m [(br,0)] Output
   (Bounds 0%nat ltac:(lia)) (Bounds 1%nat ltac:(lia)) (Bounds 2%nat ltac:(lia))
   (Bounds 3%nat ltac:(lia)) (Bounds 4%nat ltac:(lia)) Rep Sep FrameInv)
   as (mf & Call & Final & RepF & Frame).
 change (rep rho [(br,0)]
   (sregs (fst (rsel rho (lay [(br,0)]) (local_write_result bd (Ptrofs.repr base))))) mf) in RepF.
 destruct (local_write_selected_storage rho (lay [(br,0)]) bd (Ptrofs.repr base)) as [Count Storage].
 destruct (rep_free_region rho [(br,0)] _ mf 0 40 RepF ltac:(rewrite Count;lia) Storage) as [_ FreeF].
 exists mf;split;[exact Call|];split;[exact Final|];split;[exact FreeF|].
 eapply lframe_implies;[exact Frame|];intros b pos [NR NE] HV;split;[exact HV|];split;[|exact NE].
 intro Foot;apply local_writer_foot_owner in Foot;contradiction.
Qed.

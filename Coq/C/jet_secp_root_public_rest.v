(** Discharge every public-body call premise from general frames and owned locals. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_root_public_entry C.jet_secp_root_public_body C.jet_secp_root_function_literal
 C.jet_secp_root_result_write C.jet_secp_root_literal C.jet_secp_multiply_input_reader
 C.jet_secp_rescale_public_reads C.jet_secp_curve_frame C.jet_secp_square_spec_bridge
 C.jet_secp_multiply_normalize_bridge C.jet_secp_point_three_reads C.jet_secp_canonical_normalize.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_square_root Simplicity.Translate.encode canonical_fe_normalize
 root_reader_candidate root_reader_flag square_reader_rho.

Theorem exec_root_public_rest_owned le m0 bd base bw outedge cursor N bi edge rc
 (x : Ty.tySem (Word 8)) m br ba bl :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 write_frame_at m0 bd base bw outedge cursor N -> 257<=N ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
 0<=rc -> rc+256<=Int64.max_unsigned ->
 Mem.range_perm m br 0 40 Cur Freeable -> Mem.range_perm m ba 0 40 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
 br<>bl -> ba<>bl -> br<>ba -> xsep (extA m0 bd bw bi) [(br,0);(ba,0);(bl,0)] ->
 finv m0 bd base bw outedge cursor N bi m false [] -> exists mf,
 Clight2.exec_stmt secp_ge (root_public_env bl br ba) le m root_public_rest E0
  (root_public_final_temps le (root_reader_flag x)) mf (Out_return (Some (Vint Int.one,tint))) /\
 finv m0 bd base bw outedge cursor N bi mf true
  (Simplicity.Translate.encode (@literal_fe_square_root Simplicity.Alg.CoreFunSem x)) /\
 Mem.range_perm mf br 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\
 lframe (rescale_locals_outside m0 bd bw bi br ba bl) m mf.
Proof.
 intros HD HO HN HX Hrc HM FR FA FL Source RL AL RA Sep Fin.
 assert (SepA : xsep (extA m0 bd bw bi) [(ba,0);(bl,0)]).
 { intros [|[|i]] HI;[exact (Sep 1%nat ltac:(cbn;lia))|exact (Sep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
 assert (OutR : ~extA m0 bd bw bi br) by exact (Sep 0%nat ltac:(cbn;lia)).
 assert (OutA : ~extA m0 bd bw bi ba) by exact (Sep 1%nat ltac:(cbn;lia)).
 assert (OutL : ~extA m0 bd bw bi bl) by exact (Sep 2%nat ltac:(cbn;lia)).
 destruct (eval_read_fe_with_cursor m0 bd base bw outedge cursor N bi edge rc x m ba bl
  HO ltac:(lia) HX Hrc HM FA FL Source AL SepA Fin)
  as (mr & Read & FieldA & FAR & FLR & SourceR & FinR & FrameR).
 change (fe_at mr ba 0 (point_canonical_limbs x)) in FieldA.
 rewrite rescale_reader_limbs in FieldA.
 assert (VR : Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FR 0);lia).
 pose proof (reader_preserves_other (extA m0 bd bw bi) ba bl bi (Ptrofs.repr edge) m mr br
  RA RL OutR VR FrameR) as KeepR.
 assert (FRR : Mem.range_perm mr br 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FR|exact KeepR|];intros;reflexivity. }
 destruct (eval_root_function_literal x mr br ba ltac:(congruence) FieldA FAR FRR)
  as (mn & Root & Result & Bound & Candidate & Literal & FAN & FRN & FrameN).
 assert (FinN : finv m0 bd base bw outedge cursor N bi mn false []).
 { eapply finv_stable;[exact HO|exact FinR|].
   eapply lframe_implies;[exact FrameN|];intros b pos HE HV;split;intro EQ;subst b;contradiction. }
 assert (FLN : Mem.range_perm mn bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FLR|exact FrameN|];intros;split;congruence. }
 destruct (eval_root_result_writes m0 bd base bw outedge cursor N bi mn br (root_reader_candidate x)
  (root_reader_flag x) HO HN FinN Bound Result FRN OutR)
  as (mt & mf & Tag & Payload & Final & FRF & FrameW).
 assert (FAF : Mem.range_perm mf ba 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FAN|exact FrameW|];intros;split;congruence. }
 assert (FLF : Mem.range_perm mf bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FLN|exact FrameW|];intros;split;congruence. }
 exists mf;split.
 - eapply exec_root_public_rest_from_calls;eassumption.
 - split;[rewrite Literal;exact Final|];split;[exact FRF|];split;[exact FAF|];split;[exact FLF|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FrameR|];intros b pos (NR & NA & NL & NE) HV.
     split;[exact HV|];split;[|exact NE].
     intro Foot;apply two_read_foot_owner in Foot;destruct Foot;contradiction.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact FrameN|];intros b pos (NR & NA & NL & NE) HV;split;assumption.
     * eapply lframe_implies;[exact FrameW|];intros b pos (NR & NA & NL & NE) HV;split;assumption.
Qed.

(** Five arbitrary input words through the actual point and affine readers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_readBit_layout C.jet_sx_mem C.jet_sx_exec C.jet_sx_state C.jet_secp_frame C.jet_secp_fe_nv
 C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run C.jet_secp_public_body C.jet_secp_read_gej_fields
 C.jet_secp_read_ge_fields C.jet_secp_point_three_reads C.jet_secp_point_source_preservation
 C.jet_secp_multiply_input_reader C.jet_secp_multiply_writer_bridge C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize C.jet_secp_rescale_public_reads.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero canonical_fe_normalize.

Theorem eval_mixed_public_reads m0 bd dbase bw outedge cursor N bi edge rc
    (x y z u v : tySem (Word 8)) m bp ba bl :
 write_frame_at m0 bd dbase bw outedge cursor N -> 768<=N ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
 frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
 frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
 frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits u)) ->
 frame_input_cells_at m0 bi edge (rc+1024) (map Some (frame_input_word_bits v)) ->
 0<=rc -> rc+1280<=Int64.max_unsigned ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
 bp<>bl -> ba<>bl -> bp<>ba -> xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(bl,0)] ->
 finv m0 bd dbase bw outedge cursor N bi m false [] ->
 exists mr ms,
 Clight2.eval_funcall secp_ge m (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
 Clight2.eval_funcall secp_ge mr (Internal f_read_ge) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef /\
 fe_at ms bp 0 (words5 (square_reader_rho x)) /\ fe_at ms bp 40 (words5 (square_reader_rho y)) /\
 fe_at ms bp 80 (words5 (square_reader_rho z)) /\
 fe_at ms ba 0 (words5 (square_reader_rho u)) /\ fe_at ms ba 40 (words5 (square_reader_rho v)) /\
 Mem.load Mint32 ms bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) /\
 Mem.load Mint32 ms ba 80=Some (Vint Int.zero) /\
 Mem.range_perm ms bp 0 128 Cur Freeable /\ Mem.range_perm ms ba 0 88 Cur Freeable /\
 Mem.range_perm ms bl 0 16 Cur Freeable /\ finv m0 bd dbase bw outedge cursor N bi ms false [] /\
 lframe (rescale_locals_outside m0 bd bw bi bp ba bl) m ms.
Proof.
 intros HO HN HX HY HZ HU HV Hrc HM HFP HFA HFL HSource HPL HAL HPA HSep HFin.
 assert (HSP : xsep (extA m0 bd bw bi) [(bp,0);(bl,0)]).
 { intros [|[|r]] HI;[exact (HSep 0%nat ltac:(cbn;lia))|exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
 assert (HSA : xsep (extA m0 bd bw bi) [(ba,0);(bl,0)]).
 { intros [|[|r]] HI;[exact (HSep 1%nat ltac:(cbn;lia))|exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
 assert (HInvP : invA m0 bd dbase bw outedge cursor N bi rc false [] 768
    (read_fe_rho (frame_input_word_bits x) rc) [] m).
 { split;[reflexivity|];split;[exact HFin|];split;[exact HN|cbn;lia]. }
 destruct (eval_read_gej_canonical_fields m0 bd dbase bw outedge cursor N 768 bi edge rc x y z m bp bl
    HO HX HY HZ Hrc ltac:(lia) HFP HFL HSource HPL HSP HInvP)
   as (mr & CPoint & FX & FY & FZ & FlagP & SrcR & FPR & FLR & InvR & FrameP).
 assert (HVA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (HFA 0);lia).
 assert (HAF : lframe (fun b _=>b=ba) m mr).
 { eapply lframe_implies;[exact FrameP|];intros b pos -> HB.
   unfold secp_locals_outside;repeat split;try congruence;exact (HSep 1%nat ltac:(cbn;lia)). }
 assert (FAR : Mem.range_perm mr ba 0 88 Cur Freeable).
 { intros pos HP;apply (proj1 (proj2 HAF));[exact HVA|reflexivity|apply HFA;exact HP]. }
 destruct InvR as [_ [FinR _]].
 change (finv m0 bd dbase bw outedge cursor N bi mr false []) in FinR.
 assert (HInvA : invA m0 bd dbase bw outedge cursor N bi (rc+768) false [] 512
    (read_fe_rho (frame_input_word_bits u) (rc+768)) [] mr).
 { split;[reflexivity|];split;[exact FinR|];split;cbn;lia. }
 replace (rc+1024) with (rc+768+256) in HV by lia.
 destruct (eval_read_ge_canonical_fields m0 bd dbase bw outedge cursor N 512 bi edge (rc+768) u v mr ba bl
    HO HU HV ltac:(lia) ltac:(lia) FAR FLR SrcR HAL HSA HInvA)
   as (ms & CAffine & FU & FV & FlagA & SrcS & FAS & FLS & InvS & FrameA).
 assert (HVP : Mem.valid_block mr bp) by (eapply Mem.perm_valid_block;apply (FPR 0);lia).
 assert (HPF : lframe (fun b _=>b=bp) mr ms).
 { eapply lframe_implies;[exact FrameA|];intros b pos -> HB.
   unfold secp_locals_outside;repeat split;try congruence;exact (HSep 0%nat ltac:(cbn;lia)). }
 destruct InvS as [_ [FinS _]].
 change (finv m0 bd dbase bw outedge cursor N bi ms false []) in FinS.
 rewrite !rescale_reader_limbs in FX,FY,FZ,FU,FV.
 exists mr,ms;split;[exact CPoint|];split;[exact CAffine|].
 split;[eapply fe_at_on_unchanged_block;[exact FX|exact HPF]|].
 split;[eapply fe_at_on_unchanged_block;[exact FY|exact HPF]|].
 split;[eapply fe_at_on_unchanged_block;[exact FZ|exact HPF]|].
 split;[exact FU|];split;[exact FV|];split.
 { rewrite (proj1 HPF Mint32 bp 120 HVP);[exact FlagP|intros;reflexivity]. }
 split;[exact FlagA|];split.
 { intros pos HP;apply (proj1 (proj2 HPF));[exact HVP|reflexivity|apply FPR;exact HP]. }
 split;[exact FAS|];split;[exact FLS|];split;[exact FinS|].
 eapply lframe_trans;[eapply lframe_implies;[exact FrameP|]|eapply lframe_implies;[exact FrameA|]];
   intros b pos (NP & NA & NL & NE) HB;unfold secp_locals_outside;repeat split;assumption.
Qed.

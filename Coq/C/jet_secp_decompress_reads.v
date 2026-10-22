(** Parity then field through the original readers, at arbitrary input cursors. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Translate Simplicity.Bit.
Require Import C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_readBit_layout C.jet_secp_bit_reader_owned C.jet_secp_multiply_input_reader
 C.jet_secp_rescale_public_reads C.jet_secp_curve_frame C.jet_secp_square_spec_bridge
 C.jet_secp_multiply_normalize_bridge C.jet_secp_point_three_reads C.jet_secp_canonical_normalize.
Require C.jets.
Import ListNotations.
Local Notation Bit := (Ty.Sum Ty.Unit Ty.Unit).
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode canonical_fe_normalize square_reader_rho.

Lemma decompress_input_windows m bi edge rc (odd : Ty.tySem Bit) (x : Ty.tySem (Word 8)) :
 frame_input_cells_at m bi edge rc (@Simplicity.Translate.encode (Ty.Prod Bit (Word 8)) (odd,x)) ->
 frame_input_bit_at m bi edge rc (Bit.toBool odd) /\
 frame_input_cells_at m bi edge (rc+1) (map Some (frame_input_word_bits x)).
Proof.
 change (@Simplicity.Translate.encode (Ty.Prod Bit (Word 8)) (odd,x)) with
   (@Simplicity.Translate.encode Bit odd ++ @Simplicity.Translate.encode (Word 8) x).
 assert (BitEncoding : @Simplicity.Translate.encode Bit odd=[Some (Bit.toBool odd)])
   by (destruct odd as [[]|[]];reflexivity).
 rewrite BitEncoding,frame_input_cells_at_app,encode_word.
 intros [Head Tail];split;[|exact Tail].
 specialize (Head 0%nat (Some (Bit.toBool odd)) eq_refl).
 change (frame_input_bit_at m bi edge (rc+0) (Bit.toBool odd)) in Head.
 rewrite Z.add_0_r in Head;exact Head.
Qed.

Theorem eval_decompress_readers m0 bd base bw outedge cursor N bi edge rc
 (odd : Ty.tySem Bit) (x : Ty.tySem (Word 8)) m bx br bl :
 write_frame_at m0 bd base bw outedge cursor N -> 513<=N ->
 frame_input_cells_at m0 bi edge rc (@Simplicity.Translate.encode (Ty.Prod Bit (Word 8)) (odd,x)) ->
 0<=rc -> rc+257<=Int64.max_unsigned ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
 bx<>bl -> br<>bl -> bx<>br -> xsep (extA m0 bd bw bi) [(bx,0);(br,0);(bl,0)] ->
 finv m0 bd base bw outedge cursor N bi m false [] -> exists mt mr,
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_readBit) [Vptr bl Ptrofs.zero] E0 mt
   (Vint (bit_int (Bit.toBool odd))) /\
 Clight2.eval_funcall secp_ge mt (Internal f_read_fe) [Vptr bx Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
 fe_at mr bx 0 (words5 (square_reader_rho x)) /\
 Mem.range_perm mr bx 0 40 Cur Freeable /\ Mem.range_perm mr br 0 88 Cur Freeable /\
 Mem.range_perm mr bl 0 16 Cur Freeable /\
 finv m0 bd base bw outedge cursor N bi mr false [] /\
 lframe (rescale_locals_outside m0 bd bw bi bx br bl) m mr.
Proof.
 intros Output Cap Input RC Max XF RF LF Source XL RL XR Sep Inv.
 assert (OutX : ~extA m0 bd bw bi bx) by exact (Sep 0%nat ltac:(cbn;lia)).
 assert (OutR : ~extA m0 bd bw bi br) by exact (Sep 1%nat ltac:(cbn;lia)).
 assert (OutL : ~extA m0 bd bw bi bl) by exact (Sep 2%nat ltac:(cbn;lia)).
 pose proof (finv_input m0 bd base bw outedge cursor N bi m [] edge rc _ Inv Input) as CurrentInput.
 destruct (decompress_input_windows m bi edge rc odd x CurrentInput) as [Parity WordInput].
 destruct (eval_secp_readBit_owned m bl bi edge rc (Bit.toBool odd) RC ltac:(lia) Source Parity LF)
   as (mt & BitCall & SourceT & LFT & FrameT).
 assert (XFT : Mem.range_perm mt bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact XF|exact FrameT|];intros;exact XL. }
 assert (RFT : Mem.range_perm mt br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact RF|exact FrameT|];intros;exact RL. }
 assert (InvT : finv m0 bd base bw outedge cursor N bi mt false []).
 { eapply finv_stable;[exact Output|exact Inv|].
   eapply lframe_implies;[exact FrameT|];intros b pos HE VB;intro EQ;subst b;contradiction. }
 destruct (decompress_input_windows m0 bi edge rc odd x Input) as [_ OriginalWord].
 assert (SepX : xsep (extA m0 bd bw bi) [(bx,0);(bl,0)]).
 { intros [|[|r]] HI;[exact OutX|exact OutL|cbn in HI;lia]. }
 destruct (eval_read_fe_with_cursor m0 bd base bw outedge cursor N bi edge (rc+1) x mt bx bl
   Output ltac:(lia) OriginalWord ltac:(lia) ltac:(lia) XFT LFT SourceT XL SepX InvT)
   as (mr & FieldCall & Field & XFR & LFR & SourceR & InvR & FrameR).
 change (fe_at mr bx 0 (point_canonical_limbs x)) in Field.
 rewrite rescale_reader_limbs in Field.
 assert (VR : Mem.valid_block mt br) by (eapply Mem.perm_valid_block;apply (RFT 0);lia).
 pose proof (reader_preserves_other (extA m0 bd bw bi) bx bl bi (Ptrofs.repr edge) mt mr br
   ltac:(congruence) RL OutR VR FrameR) as KeepR.
 assert (RFR : Mem.range_perm mr br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact RFT|exact KeepR|];intros;reflexivity. }
 exists mt,mr;split;[exact BitCall|];split;[exact FieldCall|];split;[exact Field|].
 split;[exact XFR|];split;[exact RFR|];split;[exact LFR|];split;[exact InvR|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact FrameT|];intros b pos (NX & NR & NL & NE) VB;exact NL.
 - eapply lframe_implies;[exact FrameR|];intros b pos (NX & NR & NL & NE) VB.
   split;[exact VB|];split;[|exact NE].
   intro Foot;apply two_read_foot_owner in Foot;destruct Foot;contradiction.
Qed.

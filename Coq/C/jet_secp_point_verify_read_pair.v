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
Require Import C.jet_secp_wrapper_run C.jet_secp_scalar_public_rest C.jet_sx_rep.
Require Import C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_canonical_scalar C.jet_toZ C.jet_secp_scalar_reader_set.
Require Import C.jet_secp_decompress_reads C.jet_secp_read_fe_cursor_capacity.
Import ListNotations.
Local Notation Bit := (Ty.Sum Ty.Unit Ty.Unit).
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode canonical_fe_normalize square_reader_rho.

Theorem eval_decompress_readers_capacity m0 bd base bw outedge cursor N bi edge rc
 (odd : Ty.tySem Bit) (x : Ty.tySem (Word 8)) m bx br bl :
 write_frame_at m0 bd base bw outedge cursor N -> 0<=N ->
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
 frame_fields_at mr bl 0 bi edge (rc+257) /\
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
 destruct (eval_read_fe_with_cursor_capacity m0 bd base bw outedge cursor N 0 bi edge (rc+1) x mt bx bl
   Output ltac:(lia) ltac:(lia) OriginalWord ltac:(lia) ltac:(lia) XFT LFT SourceT XL SepX InvT)
   as (mr & FieldCall & Field & XFR & LFR & SourceR & InvR & FrameR).
 change (fe_at mr bx 0 (point_canonical_limbs x)) in Field.
 rewrite rescale_reader_limbs in Field.
 assert (VR : Mem.valid_block mt br) by (eapply Mem.perm_valid_block;apply (RFT 0);lia).
 pose proof (reader_preserves_other (extA m0 bd bw bi) bx bl bi (Ptrofs.repr edge) mt mr br
   ltac:(congruence) RL OutR VR FrameR) as KeepR.
 assert (RFR : Mem.range_perm mr br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact RFT|exact KeepR|];intros;reflexivity. }
 exists mt,mr;split;[exact BitCall|];split;[exact FieldCall|];split;[exact Field|];split.
 - replace (rc+257) with (rc+1+256) by lia;exact SourceR.
 - split;[exact XFR|];split;[exact RFR|];split;[exact LFR|];split;[exact InvR|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FrameT|];intros b pos (NX & NR & NL & NE) VB;exact NL.
   + eapply lframe_implies;[exact FrameR|];intros b pos (NX & NR & NL & NE) VB.
   split;[exact VB|];split;[|exact NE].
   intro Foot;apply two_read_foot_owner in Foot;destruct Foot;contradiction.
Qed.

Theorem eval_point_verify_read_pair m0 bd base bw outedge cursor N bi edge rc
 (raw x:Ty.tySem (Word 8)) (odd:Ty.tySem Bit) m bk bx br bl :
 write_frame_at m0 bd base bw outedge cursor N ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits raw)) ->
 frame_input_cells_at m0 bi edge (rc+256) (@Simplicity.Translate.encode (Ty.Prod Bit (Word 8)) (odd,x)) ->
 0<=rc -> rc+513<=Int64.max_unsigned ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
 Mem.range_perm m br 0 88 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
 frame_fields_at m bl 0 bi edge rc -> NoDup [bk;bx;br;bl] ->
 xsep (extA m0 bd bw bi) [(bk,0);(bx,0);(br,0);(bl,0)] ->
 finv m0 bd base bw outedge cursor N bi m false [] -> exists ms mt mf,
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar) [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef /\
 Clight2.eval_funcall secp_ge ms (Internal C.jets.f_readBit) [Vptr bl Ptrofs.zero] E0 mt
  (Vint (bit_int (Bit.toBool odd))) /\
 Clight2.eval_funcall secp_ge mt (Internal f_read_fe) [Vptr bx Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 fe_at mf bx 0 (words5 (square_reader_rho x)) /\
 frame_fields_at mf bl 0 bi edge (rc+513) /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
 Mem.range_perm mf br 0 88 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
 finv m0 bd base bw outedge cursor N bi mf false [] /\
 lframe (fun b _=>b<>bk /\ b<>bx /\ b<>br /\ b<>bl /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Raw Point RC Max FK FX FR FL Source Distinct Sep Fin.
 assert (Apart:bk<>bx /\ bk<>br /\ bk<>bl /\ bx<>br /\ bx<>bl /\ br<>bl).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Apart as (KX & KR & KL & XR & XL & RL).
 assert (Cap:0<=N) by (destruct Output as (_ & _ & _ & Bound & _);lia).
 assert (SepK:xsep (extA m0 bd bw bi) [(bk,0);(bl,0)]).
 { intros [|[|r]] Index;[exact (Sep 0%nat ltac:(cbn;lia))|
   exact (Sep 3%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 assert (Inv:invA m0 bd base bw outedge cursor N bi rc false [] 0
  (read_fe_rho (frame_input_word_bits raw) rc) [] m).
 { split;[reflexivity|];split;[exact Fin|];split;[exact Cap|cbn;lia]. }
 destruct (eval_read_scalar_canonical_with_source m0 bd base bw outedge cursor N 0 bi edge rc raw
  m bk bl Output Raw RC ltac:(lia) FK FL Source KL SepK Inv)
  as (ms & Scalar & Input & SourceS & FKS & FLS & InvS & FrameK).
 assert (SameX:lframe (fun b _=>b=bx) m ms).
 { eapply lframe_implies;[exact FrameK|].
   intros b pos Same Valid;subst b;unfold frame;split;[exact Valid|];split.
   - apply scalar_locals_not_foot;congruence.
   - exact (Sep 1%nat ltac:(cbn;lia)). }
 assert (SameR:lframe (fun b _=>b=br) m ms).
 { eapply lframe_implies;[exact FrameK|].
   intros b pos Same Valid;subst b;unfold frame;split;[exact Valid|];split.
   - apply scalar_locals_not_foot;congruence.
   - exact (Sep 2%nat ltac:(cbn;lia)). }
 assert (FXS:Mem.range_perm ms bx 0 40 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FX|exact SameX|intros;reflexivity]).
 assert (FRS:Mem.range_perm ms br 0 88 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FR|exact SameR|intros;reflexivity]).
 assert (SepP:xsep (extA m0 bd bw bi) [(bx,0);(br,0);(bl,0)]).
 { intros [|[|[|r]]] Index;[exact (Sep 1%nat ltac:(cbn;lia))|
   exact (Sep 2%nat ltac:(cbn;lia))|exact (Sep 3%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 destruct (eval_decompress_readers_capacity m0 bd base bw outedge cursor N bi edge (rc+256)
  odd x ms bx br bl Output Cap Point ltac:(lia) ltac:(lia) FXS FRS FLS SourceS XL RL XR SepP
  (proj1 (proj2 InvS)))
  as (mt & mf & BitCall & FieldCall & X & SourceF & FXF & FRF & FLF & FinF & FrameP).
 assert (SameK:lframe (fun b _=>b=bk) ms mf).
 { eapply lframe_implies;[exact FrameP|].
   intros b pos Same Valid;subst b;unfold rescale_locals_outside;repeat split;try congruence.
   exact (Sep 0%nat ltac:(cbn;lia)). }
 assert (InputF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))))
  by (eapply scalar_at_lframe;[exact Input|exact SameK|intros;reflexivity]).
 assert (FKF:Mem.range_perm mf bk 0 32 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FKS|exact SameK|intros;reflexivity]).
 replace (rc+256+257) with (rc+513) in SourceF by lia.
 exists ms,mt,mf;split;[exact Scalar|];split;[exact BitCall|];split;[exact FieldCall|];
 split;[exact InputF|];split;[exact X|];split;[exact SourceF|];split;[exact FKF|];
 split;[exact FXF|];split;[exact FRF|];split;[exact FLF|];split;[exact FinF|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact FrameK|].
   intros b pos (NK & NX & NR & NL & Other) Valid;unfold frame;split;[exact Valid|];split;
    [apply scalar_locals_not_foot;assumption|exact Other].
 - eapply lframe_implies;[exact FrameP|].
   intros b pos (NK & NX & NR & NL & Other) Valid;unfold rescale_locals_outside;repeat split;assumption.
Qed.

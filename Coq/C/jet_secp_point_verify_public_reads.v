(** The original six point-verifier reader calls on arbitrary valid cursors. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_readBit_layout C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_point_verify_read_pair
 C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_canonical_scalar C.jet_toZ
 C.jet_secp_fe_nv C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_point_three_reads C.jet_frame_layout C.jet_frame_inv C.jet_input_layout
 C.jet_output_layout C.jet_encoding C.jet_secp_frame C.jet_secp_square_spec_bridge C.jet_secp_multiply_normalize_bridge.
Require C.jets.
Require Import C.jet_secp_field_io_preserve C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_normalize.
Local Ltac readers_distinct Separate :=
 clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;
 cbn [In] in *;repeat split;try apply NoDup_nil;intuition congruence.

Theorem eval_point_verify_public_reads m0 bd base bw edge cursor N bi inedge rc
 (raw ng ax bxword:Ty.tySem (Word 8)) (ay bybit:Ty.tySem Simplicity.Bit.Bit) m bk bax ba bg bbx bb bl :
 write_frame_at m0 bd base bw edge cursor N ->
 frame_input_cells_at m0 bi inedge rc (map Some (frame_input_word_bits raw)) ->
 frame_input_cells_at m0 bi inedge (rc+256)
  (@Simplicity.Translate.encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (ay,ax)) ->
 frame_input_cells_at m0 bi inedge (rc+513) (map Some (frame_input_word_bits ng)) ->
 frame_input_cells_at m0 bi inedge (rc+769)
  (@Simplicity.Translate.encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (bybit,bxword)) ->
 0<=rc -> rc+1026<=Int64.max_unsigned ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bax 0 40 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bg 0 32 Cur Freeable -> Mem.range_perm m bbx 0 40 Cur Freeable -> Mem.range_perm m bb 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi inedge rc ->
 NoDup [bk;bax;ba;bg;bbx;bb;bl] ->
 xsep (extA m0 bd bw bi) [(bk,0);(bax,0);(ba,0);(bg,0);(bbx,0);(bb,0);(bl,0)] ->
 finv m0 bd base bw edge cursor N bi m false [] -> exists m1 m2 m3 m4 m5 mf,
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar) [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m1 Vundef /\
 Clight2.eval_funcall secp_ge m1 (Internal C.jets.f_readBit) [Vptr bl Ptrofs.zero] E0 m2 (Vint (bit_int (Simplicity.Bit.toBool ay))) /\
 Clight2.eval_funcall secp_ge m2 (Internal f_read_fe) [Vptr bax Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m3 Vundef /\
 Clight2.eval_funcall secp_ge m3 (Internal f_read_scalar) [Vptr bg Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m4 Vundef /\
 Clight2.eval_funcall secp_ge m4 (Internal C.jets.f_readBit) [Vptr bl Ptrofs.zero] E0 m5 (Vint (bit_int (Simplicity.Bit.toBool bybit))) /\
 Clight2.eval_funcall secp_ge m5 (Internal f_read_fe) [Vptr bbx Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 scalar_at mf bg 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) /\
 fe_at mf bax 0 (words5 (square_reader_rho ax)) /\ fe_at mf bbx 0 (words5 (square_reader_rho bxword)) /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ Mem.range_perm mf bax 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bg 0 32 Cur Freeable /\ Mem.range_perm mf bbx 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 88 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\ frame_fields_at mf bl 0 bi inedge (rc+1026) /\
 finv m0 bd base bw edge cursor N bi mf false [] /\
 lframe (fun b _=>b<>bk /\ b<>bax /\ b<>ba /\ b<>bg /\ b<>bbx /\ b<>bb /\ b<>bl /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Raw AX NG BX RC Max FK FXA FA FG FXB FB FL Source Distinct Sep Fin.
 assert (SepA:xsep (extA m0 bd bw bi) [(bk,0);(bax,0);(ba,0);(bl,0)]).
 { intros [|[|[|[|r]]]] Index;[exact (Sep 0%nat ltac:(cbn;lia))|exact (Sep 1%nat ltac:(cbn;lia))|
   exact (Sep 2%nat ltac:(cbn;lia))|exact (Sep 6%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 destruct (eval_point_verify_read_pair m0 bd base bw edge cursor N bi inedge rc raw ax ay m bk bax ba bl
  Output Raw AX RC ltac:(lia) FK FXA FA FL Source ltac:(readers_distinct Distinct) SepA Fin)
  as (m1 & m2 & m3 & ScalarA & BitA & FieldA & InputA & XA & SourceA & FKA & FXAA & FAA & FLA & FinA & FrameA).
 assert (FG3:Mem.range_perm m3 bg 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FG|exact FrameA|].
   intros;repeat split;try (readers_distinct Distinct);exact (Sep 3%nat ltac:(cbn;lia)). }
 assert (FXB3:Mem.range_perm m3 bbx 0 40 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FXB|exact FrameA|].
   intros;repeat split;try (readers_distinct Distinct);exact (Sep 4%nat ltac:(cbn;lia)). }
 assert (FB3:Mem.range_perm m3 bb 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FB|exact FrameA|].
   intros;repeat split;try (readers_distinct Distinct);exact (Sep 5%nat ltac:(cbn;lia)). }
 assert (SepB:xsep (extA m0 bd bw bi) [(bg,0);(bbx,0);(bb,0);(bl,0)]).
 { intros [|[|[|[|r]]]] Index;[exact (Sep 3%nat ltac:(cbn;lia))|exact (Sep 4%nat ltac:(cbn;lia))|
   exact (Sep 5%nat ltac:(cbn;lia))|exact (Sep 6%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 assert (BXShift:frame_input_cells_at m0 bi inedge (rc+513+256)
  (@Simplicity.Translate.encode (Ty.Prod Simplicity.Bit.Bit (Word 8)) (bybit,bxword))).
 { replace (rc+513+256) with (rc+769) by lia;exact BX. }
 destruct (eval_point_verify_read_pair m0 bd base bw edge cursor N bi inedge (rc+513) ng bxword bybit m3 bg bbx bb bl
  Output NG BXShift ltac:(lia) ltac:(lia) FG3 FXB3 FB3 FLA SourceA ltac:(readers_distinct Distinct) SepB FinA)
  as (m4 & m5 & mf & ScalarB & BitB & FieldB & InputB & XB & SourceB & FGB & FXBB & FBB & FLB & FinB & FrameB).
 assert (KeepA:lframe (fun b _=>In b [bk;bax;ba]) m3 mf).
 { eapply lframe_implies;[exact FrameB|].
   intros b pos Member Valid;cbn [In] in Member;destruct Member as [Member|[Member|[Member|Member]]];try contradiction;
   subst b;repeat split;try (readers_distinct Distinct);
   first [exact (Sep 0%nat ltac:(cbn;lia))|exact (Sep 1%nat ltac:(cbn;lia))|exact (Sep 2%nat ltac:(cbn;lia))]. }
 assert (InputAF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
   (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))))
  by (eapply scalar_at_lframe;[exact InputA|exact KeepA|intros;cbn [In];tauto]).
 assert (XAF:fe_at mf bax 0 (words5 (square_reader_rho ax)))
  by (eapply field_at_lframe;[exact XA|exact KeepA|intros;cbn [In];tauto]).
 assert (FKF:Mem.range_perm mf bk 0 32 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FKA|exact KeepA|intros;cbn [In];tauto]).
 assert (FXAF:Mem.range_perm mf bax 0 40 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FXAA|exact KeepA|intros;cbn [In];tauto]).
 assert (FAF:Mem.range_perm mf ba 0 88 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FAA|exact KeepA|intros;cbn [In];tauto]).
 replace (rc+513+513) with (rc+1026) in SourceB by lia.
 exists m1,m2,m3,m4,m5,mf;
 split;[exact ScalarA|];split;[exact BitA|];split;[exact FieldA|];split;[exact ScalarB|];split;[exact BitB|];split;[exact FieldB|];
 split;[exact InputAF|];split;[exact InputB|];split;[exact XAF|];split;[exact XB|];
 split;[exact FKF|];split;[exact FXAF|];split;[exact FAF|];split;[exact FGB|];split;[exact FXBB|];split;[exact FBB|];split;[exact FLB|];
 split;[exact SourceB|];split;[exact FinB|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact FrameA|].
   intros b pos (NK & NX & NA & NoG & NBX & NB & NL & Other) Valid;repeat split;assumption.
 - eapply lframe_implies;[exact FrameB|].
   intros b pos (NK & NX & NA & NoG & NBX & NB & NL & Other) Valid;repeat split;assumption.
Qed.

Lemma point_verify_bit_reader_allowed : allowed_call field_io_helpers (Internal C.jets.f_readBit).
Proof. exists C.jets._readBit,C.jets.f_readBit;split;[vm_compute;reflexivity|reflexivity]. Qed.
Lemma point_verify_bit_reader_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_readBit) args t mf result -> readonly_preserved m mf.
Proof.
 intro Call;exact (proj2 (internal_exec_preserved _ _ field_io_helpers_ok)
  m _ args t mf result Call point_verify_bit_reader_allowed).
Qed.

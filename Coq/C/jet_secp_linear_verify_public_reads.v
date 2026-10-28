(** The four original linear_verify_1 reader calls, with zero output
    capacity and preservation of both previously read operands. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_readBit_layout C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_linear_verify_read_pair
 C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_canonical_scalar C.jet_toZ
 C.jet_secp_fe_nv C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_point_three_reads C.jet_frame_layout C.jet_frame_inv C.jet_input_layout
 C.jet_output_layout C.jet_encoding C.jet_secp_frame.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_normalize.
Theorem eval_linear_verify_public_reads m0 bd base bw edge cursor N bi inedge rc
 (raw ng ax ay bxword byword:Ty.tySem (Word 8)) m bk ba bg bb bl :
 write_frame_at m0 bd base bw edge cursor N ->
 frame_input_cells_at m0 bi inedge rc (map Some (frame_input_word_bits raw)) ->
 frame_input_cells_at m0 bi inedge (rc+256) (map Some (frame_input_word_bits ax)) ->
 frame_input_cells_at m0 bi inedge (rc+512) (map Some (frame_input_word_bits ay)) ->
 frame_input_cells_at m0 bi inedge (rc+768) (map Some (frame_input_word_bits ng)) ->
 frame_input_cells_at m0 bi inedge (rc+1024) (map Some (frame_input_word_bits bxword)) ->
 frame_input_cells_at m0 bi inedge (rc+1280) (map Some (frame_input_word_bits byword)) ->
 0<=rc -> rc+1536<=Int64.max_unsigned ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bg 0 32 Cur Freeable -> Mem.range_perm m bb 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi inedge rc ->
 NoDup [bk;ba;bg;bb;bl] ->
 xsep (extA m0 bd bw bi) [(bk,0);(ba,0);(bg,0);(bb,0);(bl,0)] ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 exists m1 m2 m3 mf,
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar) [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m1 Vundef /\
 Clight2.eval_funcall secp_ge m1 (Internal f_read_ge) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m2 Vundef /\
 Clight2.eval_funcall secp_ge m2 (Internal f_read_scalar) [Vptr bg Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m3 Vundef /\
 Clight2.eval_funcall secp_ge m3 (Internal f_read_ge) [Vptr bb Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 scalar_at mf bg 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) /\
 fe_at mf ba 0 (point_canonical_limbs ax) /\ fe_at mf ba 40 (point_canonical_limbs ay) /\
 Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
 fe_at mf bb 0 (point_canonical_limbs bxword) /\ fe_at mf bb 40 (point_canonical_limbs byword) /\
 Mem.load Mint32 mf bb 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bg 0 32 Cur Freeable /\ Mem.range_perm mf bb 0 88 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\ frame_fields_at mf bl 0 bi inedge (rc+1536) /\
 finv m0 bd base bw edge cursor N bi mf false [] /\
 lframe (fun b _=>b<>bk /\ b<>ba /\ b<>bg /\ b<>bb /\ b<>bl /\ ~extA m0 bd bw bi b) m mf.
Proof.
 intros Output Raw AX AY NG BX BY RC Max FK FA FG FB FL Source Separate Sep Fin.
 assert (Distinct:bk<>ba /\ bk<>bg /\ bk<>bb /\ bk<>bl /\ ba<>bg /\ ba<>bb /\ ba<>bl /\ bg<>bb /\ bg<>bl /\ bb<>bl).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 destruct Distinct as (KA & KG & KB & KL & AG & AB & AL & GB & GL & BL).
 assert (SepA:xsep (extA m0 bd bw bi) [(bk,0);(ba,0);(bl,0)]).
 { intros [|[|[|r]]] Index;[exact (Sep 0%nat ltac:(cbn;lia))|
   exact (Sep 1%nat ltac:(cbn;lia))|exact (Sep 4%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 destruct (eval_linear_verify_read_pair m0 bd base bw edge cursor N bi inedge rc raw ax ay m bk ba bl
   Output Raw AX AY RC ltac:(lia) FK FA FL Source KL AL KA SepA Fin)
   as (m1 & m2 & ScalarA & PointA & InputA & XA & YA & FlagA & FKA & FAA & FLA & SourceA & FinA & FrameA).
 assert (FG2:Mem.range_perm m2 bg 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FG|exact FrameA|].
   intros;repeat split;try congruence;exact (Sep 2%nat ltac:(cbn;lia)). }
 assert (FB2:Mem.range_perm m2 bb 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FB|exact FrameA|].
   intros;repeat split;try congruence;exact (Sep 3%nat ltac:(cbn;lia)). }
 assert (SepB:xsep (extA m0 bd bw bi) [(bg,0);(bb,0);(bl,0)]).
 { intros [|[|[|r]]] Index;[exact (Sep 2%nat ltac:(cbn;lia))|
   exact (Sep 3%nat ltac:(cbn;lia))|exact (Sep 4%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 assert (BXShift:frame_input_cells_at m0 bi inedge (rc+768+256) (map Some (frame_input_word_bits bxword)))
   by (replace (rc+768+256) with (rc+1024) by lia;exact BX).
 assert (BYShift:frame_input_cells_at m0 bi inedge (rc+768+512) (map Some (frame_input_word_bits byword)))
   by (replace (rc+768+512) with (rc+1280) by lia;exact BY).
 destruct (eval_linear_verify_read_pair m0 bd base bw edge cursor N bi inedge (rc+768) ng bxword byword m2 bg bb bl
   Output NG BXShift BYShift ltac:(lia) ltac:(lia) FG2 FB2 FLA SourceA GL BL GB SepB FinA)
   as (m3 & mf & ScalarB & PointB & InputB & XB & YB & FlagB & FGB & FBB & FLB & SourceB & FinB & FrameB).
 assert (SameK:lframe (fun b _=>b=bk) m2 mf).
 { eapply lframe_implies;[exact FrameB|].
   intros b pos Same Valid;subst b;repeat split;try congruence;exact (Sep 0%nat ltac:(cbn;lia)). }
 assert (SameA:lframe (fun b _=>b=ba) m2 mf).
 { eapply lframe_implies;[exact FrameB|].
   intros b pos Same Valid;subst b;repeat split;try congruence;exact (Sep 1%nat ltac:(cbn;lia)). }
 assert (InputAF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
   (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))))
   by (eapply scalar_at_lframe;[exact InputA|exact SameK|intros;reflexivity]).
 assert (XAF:fe_at mf ba 0 (point_canonical_limbs ax))
   by (eapply field_at_lframe;[exact XA|exact SameA|intros;reflexivity]).
 assert (YAF:fe_at mf ba 40 (point_canonical_limbs ay))
   by (eapply field_at_lframe;[exact YA|exact SameA|intros;reflexivity]).
 assert (ValidA:Mem.valid_block m2 ba) by (eapply Mem.perm_valid_block;apply (FAA 0);lia).
 assert (FlagAF:Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
 { rewrite (proj1 SameA Mint32 ba 80 ValidA ltac:(intros;reflexivity));exact FlagA. }
 assert (FKF:Mem.range_perm mf bk 0 32 Cur Freeable)
   by (eapply curve_keep_free;[clear;lia|exact FKA|exact SameK|intros;reflexivity]).
 assert (FAF:Mem.range_perm mf ba 0 88 Cur Freeable)
   by (eapply curve_keep_free;[clear;lia|exact FAA|exact SameA|intros;reflexivity]).
 replace (rc+768+768) with (rc+1536) in SourceB by lia.
 exists m1,m2,m3,mf;
 split;[exact ScalarA|];split;[exact PointA|];split;[exact ScalarB|];split;[exact PointB|];
 split;[exact InputAF|];split;[exact InputB|];split;[exact XAF|];split;[exact YAF|];split;[exact FlagAF|];
 split;[exact XB|];split;[exact YB|];split;[exact FlagB|];
 split;[exact FKF|];split;[exact FAF|];split;[exact FGB|];split;[exact FBB|];split;[exact FLB|];
 split;[exact SourceB|];split;[exact FinB|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact FrameA|].
   intros b pos (NK & NA & NoG & NB & NL & Other) Valid;repeat split;assumption.
 - eapply lframe_implies;[exact FrameB|].
   intros b pos (NK & NA & NoG & NB & NL & Other) Valid;repeat split;assumption.
Qed.

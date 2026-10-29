(** Actual short-circuit decompression, retaining both arithmetic operands. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_root_chain_numeric C.jet_secp_root_check
 C.jet_secp_decompress_numeric C.jet_secp_decompress_body C.jet_secp_decompress_readback
 C.jet_secp_point_verify_guards C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge decompress_y_words.

Theorem eval_point_verify_decompress e le wa wb (ax bxword:Ty.tySem (Word 8))
 (ay bybit:Ty.tySem Simplicity.Bit.Bit) m bax ba bbx bb :
 e!_a__1=Some (ba,Tstruct __6121 noattr) -> e!_b=Some (bb,Tstruct __6121 noattr) ->
 e!_ax=Some (bax,Tstruct __5467 noattr) -> e!_bx=Some (bbx,Tstruct __5467 noattr) ->
 e!_secp256k1_ge_set_xo_var=None ->
 le!_ay=Some (Vint (bit_int (Simplicity.Bit.toBool ay))) ->
 le!_by=Some (Vint (bit_int (Simplicity.Bit.toBool bybit))) ->
 NoDup [bax;ba;bbx;bb] -> root_words_match wa ax -> root_words_match wb bxword ->
 fe_at m bax 0 (words5 wa) -> fe_at m bbx 0 (words5 wb) ->
 Mem.range_perm m bax 0 40 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bbx 0 40 Cur Freeable -> Mem.range_perm m bb 0 88 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m point_verify_guards E0
  (point_verify_guard_temps le (root_check_flag (decompress_root_words wa))
   (root_check_flag (decompress_root_words wb))) mf Out_normal /\
 fe_at mf ba 0 (words5 wa) /\ fe_at mf ba 40 (words5 (decompress_y_words wa (Simplicity.Bit.toBool ay))) /\
 Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
 (if root_check_flag (decompress_root_words wa) then
   fe_at mf bb 0 (words5 wb) /\ fe_at mf bb 40 (words5 (decompress_y_words wb (Simplicity.Bit.toBool bybit))) /\
   Mem.load Mint32 mf bb 80=Some (Vint Int.zero) else True) /\
 Mem.range_perm mf bax 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bbx 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bax /\ b<>ba /\ b<>bbx /\ b<>bb) m mf /\ readonly_preserved m mf.
Proof.
 intros EA EB EAX EBX EG AY BY Distinct MatchA MatchB InputA InputB FXA FA FXB FB.
 assert (Apart:bax<>ba /\ bax<>bbx /\ bax<>bb /\ ba<>bbx /\ ba<>bb /\ bbx<>bb).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Apart as (XA & XX & XB & AX & AB & BB).
 destruct (eval_decompress_retained wa ax ay m bax ba XA MatchA InputA FXA FA)
  as (ma & CallA & XAA & YAA & FlagA & BoundsA & LiteralA & CurveA & FXAA & FAA & FrameA).
 assert (InputBA:fe_at ma bbx 0 (words5 wb))
  by (eapply field_at_lframe;[exact InputB|exact FrameA|intros;split;congruence]).
 assert (FXBA:Mem.range_perm ma bbx 0 40 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FXB|exact FrameA|intros;split;congruence]).
 assert (FBA:Mem.range_perm ma bb 0 88 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FB|exact FrameA|intros;split;congruence]).
 assert (ReadA:readonly_preserved m ma) by (eapply decompress_call_readonly;exact CallA).
 unfold decompress_body_return in CallA.
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
  [Vptr ba Ptrofs.zero;Vptr bax Ptrofs.zero;Vint (bit_int (Simplicity.Bit.toBool ay))] E0 ma
  (Vint (bit_int (root_check_flag (decompress_root_words wa))))) in CallA.
 destruct (root_check_flag (decompress_root_words wa)) eqn:GoodA.
 - destruct (eval_decompress_retained wb bxword bybit ma bbx bb BB MatchB InputBA FXBA FBA)
    as (mf & CallB & XBB & YBB & FlagB & BoundsB & LiteralB & CurveB & FXBB & FBB & FrameB).
   assert (XAF:fe_at mf ba 0 (words5 wa))
    by (eapply field_at_lframe;[exact XAA|exact FrameB|intros;split;congruence]).
   assert (YAF:fe_at mf ba 40 (words5 (decompress_y_words wa (Simplicity.Bit.toBool ay))))
    by (eapply field_at_lframe;[exact YAA|exact FrameB|intros;split;congruence]).
   assert (VA:Mem.valid_block ma ba) by (eapply Mem.perm_valid_block;apply (FAA 0);lia).
   assert (FlagAF:Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
   { rewrite (proj1 FrameB Mint32 ba 80 VA ltac:(intros;split;congruence));exact FlagA. }
   assert (FXAF:Mem.range_perm mf bax 0 40 Cur Freeable)
    by (eapply curve_keep_free;[clear;lia|exact FXAA|exact FrameB|intros;split;congruence]).
   assert (FAF:Mem.range_perm mf ba 0 88 Cur Freeable)
    by (eapply curve_keep_free;[clear;lia|exact FAA|exact FrameB|intros;split;congruence]).
   assert (ReadB:readonly_preserved ma mf) by (eapply decompress_call_readonly;exact CallB).
   unfold decompress_body_return in CallB.
   change (Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_ge_set_xo_var)
    [Vptr bb Ptrofs.zero;Vptr bbx Ptrofs.zero;Vint (bit_int (Simplicity.Bit.toBool bybit))] E0 mf
    (Vint (bit_int (root_check_flag (decompress_root_words wb))))) in CallB.
   exists mf;split.
   + eapply exec_point_verify_guards with (a:=true) (b:=root_check_flag (decompress_root_words wb));eassumption.
   + split;[exact XAF|];split;[exact YAF|];split;[exact FlagAF|];split.
     * split;[exact XBB|];split;[exact YBB|exact FlagB].
     * split;[exact FXAF|];split;[exact FAF|];split;[exact FXBB|];split;[exact FBB|];split.
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact FrameA|];intros b pos (NX & NA & NXB & NB) Valid;split;assumption.
          ++ eapply lframe_implies;[exact FrameB|];intros b pos (NX & NA & NXB & NB) Valid;split;assumption.
       -- eapply preserved_trans;[exact ReadA|exact ReadB].
 - exists ma;split.
   + eapply exec_point_verify_guards with (a:=false) (b:=root_check_flag (decompress_root_words wb));try eassumption;reflexivity.
   + split;[exact XAA|];split;[exact YAA|];split;[exact FlagA|];split;[exact I|];
     split;[exact FXAA|];split;[exact FAA|];split;[exact FXBA|];split;[exact FBA|];split;[|exact ReadA].
     eapply lframe_implies;[exact FrameA|];intros b pos (NX & NA & NXB & NB) Valid;split;assumption.
Qed.

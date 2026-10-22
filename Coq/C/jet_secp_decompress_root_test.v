(** Original ge_set_xo_var root call and conditional return, for both
    success and failure. The success tail is a separate caller obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_root_chain_numeric C.jet_secp_root_check C.jet_secp_rescale_literal
 C.jet_secp_decompress_literal C.jet_secp_decompress_numeric C.jet_secp_decompress_root
 C.jet_secp_root_affine_y_state C.jet_secp_decompress_statements C.jet_secp_decompress_prefix
 C.jet_secp_curve_frame C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_check_flag decompress_root_words root_chain_candidate
 literal_y_from_x rescale_field_output.

Definition decompress_root_temps le w := PTree.set _t'1
 (Vint (if root_check_flag (decompress_root_words w) then Int.one else Int.zero)) le.
Definition decompress_root_outcome w := if root_check_flag (decompress_root_words w)
 then Out_normal else Out_return (Some (Vint Int.zero,tint)).

Theorem exec_decompress_root_test_owned e le m br b3 w (x : Ty.tySem (Word 8)) :
 le!_r=Some (Vptr br Ptrofs.zero) -> e!_x3=Some (b3,curve_fe_type) ->
 e!_secp256k1_fe_sqrt_var=None -> b3<>br -> root_words_match w x ->
 fe_at m b3 0 (words5 (decompress_root_words w)) ->
 Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m decompress_root_test E0 (decompress_root_temps le w) mf
  (decompress_root_outcome w) /\
 fe_at mf br 40 (words5 (root_chain_candidate (decompress_root_words w))) /\
 square_input_bounds (root_chain_candidate (decompress_root_words w)) /\
 @literal_y_from_x Alg.CoreFunSem x=
  (if root_check_flag (decompress_root_words w)
   then inr (rescale_field_output (root_chain_candidate (decompress_root_words w))) else inl tt) /\
 Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (root_y_outside br b3) m mf.
Proof.
 intros HR E3 ER Ne Match Field F3 FR.
 destruct (eval_decompress_root w x m br b3 Ne Match Field F3 FR)
  as (mf & Root & Y & Bounds & Literal & F3F & FRF & Frame).
 assert (Call : Clight2.exec_stmt secp_ge e le m decompress_root_call E0
  (decompress_root_temps le w) mf Out_normal).
 { unfold decompress_root_call,decompress_root_temps;eapply exec_curve_call with
    (vargs:=[Vptr br (Ptrofs.repr 40);Vptr b3 Ptrofs.zero])
    (v:=Vint (if root_check_flag (decompress_root_words w) then Int.one else Int.zero)).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact ER.
   - eapply eval_Econs.
     + apply eval_decompress_field_address.
       * right;left;reflexivity.
       * exact HR.
     + reflexivity.
     + eapply eval_Econs;[apply eval_curve_local;exact E3|reflexivity|constructor].
   - exact Root. }
 exists mf;split.
 - unfold decompress_root_test,decompress_root_temps,decompress_root_outcome in *.
   destruct (root_check_flag (decompress_root_words w)) eqn:Flag.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
     * reflexivity.
     * apply exec_Sskip.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
     eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
     * reflexivity.
     * apply exec_Sreturn_some;constructor.
 - split;[exact Y|];split;[exact Bounds|];split;[exact Literal|];split;[exact F3F|];split;assumption.
Qed.

Theorem exec_decompress_failure_body e le m bx br b2 b3 w (x : Ty.tySem (Word 8)) :
 le!_x=Some (Vptr bx Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 e!_x2=Some (b2,curve_fe_type) -> e!_x3=Some (b3,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add_int=None ->
 e!_secp256k1_fe_sqrt_var=None -> NoDup [bx;br;b2;b3] -> root_words_match w x ->
 root_check_flag (decompress_root_words w)=false -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_ge_set_xo_var) E0
  (decompress_root_temps le w) mf (Out_return (Some (Vint Int.zero,tint))) /\
 fe_at mf br 0 (words5 w) /\ fe_at mf br 40 (words5 (root_chain_candidate (decompress_root_words w))) /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\ @literal_y_from_x Alg.CoreFunSem x=inl tt /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 lframe (decompress_prefix_frame bx br b2 b3) m mf.
Proof.
 intros HX HR E2 E3 EQ EM EA ER Sep Match Flag Input XF RF F2 F3.
 assert (Pairs : bx<>br /\ bx<>b3 /\ br<>b3 /\ b2<>br /\ b2<>b3).
 { repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
 destruct Pairs as (XR & X3 & R3 & N2R & N23).
 destruct (exec_decompress_prefix_owned e le m bx br b2 b3 w HX HR E2 E3 EQ EM EA Sep
  (proj1 Match) Input XF RF F2 F3)
  as (mi & Prefix & IX & RX & RootInput & Finite & XFI & RFI & F2I & F3I & FrameP).
 destruct (exec_decompress_root_test_owned e le mi br b3 w x HR E3 ER ltac:(congruence)
  Match RootInput F3I RFI) as (mf & Test & Y & Bounds & Literal & F3F & RFF & FrameR).
 unfold decompress_root_outcome in Test;rewrite Flag in Test.
 rewrite Flag in Literal.
 assert (RXF : fe_at mf br 0 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact RX|exact FrameR|].
   intros pos Range;split;[exact R3|right;left;lia]. }
 assert (XFF : Mem.range_perm mf bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact XFI|exact FrameR|];intros;split;[exact X3|left;exact XR]. }
 assert (F2F : Mem.range_perm mf b2 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F2I|exact FrameR|];intros;split;[exact N23|left;exact N2R]. }
 assert (FiniteF : Mem.load Mint32 mf br 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameR Mint32 br 80 ltac:(eapply Mem.perm_valid_block;apply (RFI 0);lia)).
   - exact Finite.
   - intros pos Range;split;[exact R3|right;right;change (80<=pos<84) in Range;lia]. }
 exists mf;split.
 - rewrite decompress_helper_body_source.
   eapply exec_statement_prefix_then_last;[exact Prefix|].
   unfold decompress_rest;eapply exec_Sseq_2;[exact Test|discriminate].
 - split;[exact RXF|];split;[exact Y|];split;[exact FiniteF|];split;[exact Literal|].
   split;[exact XFF|];split;[exact RFF|];split;[exact F2F|];split;[exact F3F|].
   eapply lframe_trans;[exact FrameP|].
   eapply lframe_implies;[exact FrameR|];intros b pos [NX [NR [N2 N3]]] _;split;[exact N3|left;exact NR].
Qed.

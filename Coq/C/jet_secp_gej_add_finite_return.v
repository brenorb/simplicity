(** Entire original projective-addition body on its finite H=0 paths.
    The H test and both early returns are shared actual statements, not a
    substituted mixed-addition call. H=0 is an internal dispatch condition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_statement_prefix C.jet_secp_gej_add_statements C.jet_secp_gej_add_preparation
 C.jet_secp_gej_add_finite_prepare C.jet_secp_gej_add_finite_difference
 C.jet_secp_mixed_difference C.jet_secp_mixed_zero C.jet_secp_mixed_zero_return
 C.jet_secp_double_all_calls C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words mixed_difference_words.

Definition gej_add_finite_return_frame (pa pb pu pv ps pt p12 p22 bh bi bx : block) (_ : Z) :=
 bx<>pa /\ bx<>pb /\ bx<>pu /\ bx<>pv /\ bx<>ps /\ bx<>pt /\ bx<>p12 /\ bx<>p22 /\ bx<>bh /\ bx<>bi.

Lemma gej_add_finite_difference_body_source : fn_body f_secp256k1_gej_add_var =
 statement_sequence (firstn 14 gej_add_statements) (gej_add_after 14).
Proof. reflexivity. Qed.
Lemma gej_add_zero_head_source : gej_add_after 14 = Ssequence mixed_zero_head (gej_add_after 15).
Proof. reflexivity. Qed.

Local Ltac separate_return_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_return_owned HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_gej_add_finite_zero_body e le m pa pb pu pv ps pt p12 p22 bh bi x y z u v w :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 le!_r=Some (Vptr pa Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 e!_u1=Some (pu,curve_fe_type) -> e!_u2=Some (pv,curve_fe_type) ->
 e!_s1=Some (ps,curve_fe_type) -> e!_s2=Some (pt,curve_fe_type) ->
 e!_z12=Some (p12,curve_fe_type) -> e!_z22=Some (p22,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
 NoDup [pa;pb;pu;pv;ps;pt;p12;p22;bh;bi] ->
 Mem.load Mint32 m pa 120=Some (Vint Int.zero) -> Mem.load Mint32 m pb 120=Some (Vint Int.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds w ->
 radix_value (gej_add_h_words x z u w) mod feP=0 ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 0 (words5 u) -> fe_at m pb 40 (words5 v) -> fe_at m pb 80 (words5 w) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
   (mixed_zero_return_temps (gej_add_finite_prepare_temps le) (gej_add_i_words y z v w)) mf (Out_return None) /\
 fe_at mf pa 0 (words5 (mixed_zero_words (gej_add_i_words y z v w) (double_output_x_words x y))) /\
 fe_at mf pa 40 (words5 (mixed_zero_words (gej_add_i_words y z v w) (double_output_y_words x y))) /\
 fe_at mf pa 80 (words5 (mixed_zero_words (gej_add_i_words y z v w) (double_output_z_words y z))) /\
 Mem.load Mint32 mf pa 120=Some (Vint (mixed_zero_flag (gej_add_i_words y z v w) y z)) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\ Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\ Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\ Mem.range_perm mf p22 0 40 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 square_input_bounds (mixed_zero_words (gej_add_i_words y z v w) (double_output_x_words x y)) /\
 square_input_bounds (mixed_zero_words (gej_add_i_words y z v w) (double_output_y_words x y)) /\
 square_input_bounds (mixed_zero_words (gej_add_i_words y z v w) (double_output_z_words y z)) /\
 lframe (gej_add_finite_return_frame pa pb pu pv ps pt p12 p22 bh bi) m mf.
Proof.
 intros PA PB PR PN EU EV ES ET E12 E22 EH EI EQ EM EN EA E0N ED EF Sep FlagA FlagB BX BY BZ BU BV BW HZ
   AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI.
 pose proof Sep as Sep0;separate_return_blocks Sep0.
 destruct (exec_gej_add_finite_difference e le m pa pb pu pv ps pt p12 p22 bh bi x y z u v w
   PA PB EU EV ES ET E12 E22 EH EI EQ EM EN EA Sep FlagA FlagB BX BY BZ BU BV BW AX AY AZ BXf BYf BZf
   FA FB FU FV FS FT F12 F22 FH FI)
   as (mp & Prepare & AXP & AYP & AZP & BXP & BYP & BZP & UP & VP & SP & TP & H & I &
     FlagAP & FlagBP & FAP & FBP & FUP & FVP & FSP & FTP & F12P & F22P & FHP & FIP &
     BoundH & BoundI & TightU & TightV & TightS & TightT & FrameP).
 assert (PAP : (gej_add_finite_prepare_temps le)!_a=Some (Vptr pa Ptrofs.zero)).
 { unfold gej_add_finite_prepare_temps;rewrite !PTree.gso by discriminate;exact PA. }
 assert (PRP : (gej_add_finite_prepare_temps le)!_r=Some (Vptr pa Ptrofs.zero)).
 { unfold gej_add_finite_prepare_temps;rewrite !PTree.gso by discriminate;exact PR. }
 assert (PNP : (gej_add_finite_prepare_temps le)!_rzr=Some (Vlong Int64.zero)).
 { unfold gej_add_finite_prepare_temps;rewrite !PTree.gso by discriminate;exact PN. }
 destruct (exec_mixed_zero_head_return e (gej_add_finite_prepare_temps le) mp pa bh bi x y z
   (gej_add_h_words x z u w) (gej_add_i_words y z v w) PAP PRP PNP EH EI E0N ED EF
   ltac:(congruence) ltac:(congruence) ltac:(congruence)
   BX BY BZ BoundH BoundI HZ FlagAP AXP AYP AZP H I FAP FHP FIP)
   as (mf & Return & XO & YO & ZO & FlagO & HO & IO & FAO & FHO & FIO & BXO & BYO & BZO & FrameR).
 assert (FBO : Mem.range_perm mf pb 0 128 Cur Freeable) by (keep_return_owned FBP FrameR).
 assert (FUO : Mem.range_perm mf pu 0 40 Cur Freeable) by (keep_return_owned FUP FrameR).
 assert (FVO : Mem.range_perm mf pv 0 40 Cur Freeable) by (keep_return_owned FVP FrameR).
 assert (FSO : Mem.range_perm mf ps 0 40 Cur Freeable) by (keep_return_owned FSP FrameR).
 assert (FTO : Mem.range_perm mf pt 0 40 Cur Freeable) by (keep_return_owned FTP FrameR).
 assert (F12O : Mem.range_perm mf p12 0 40 Cur Freeable) by (keep_return_owned F12P FrameR).
 assert (F22O : Mem.range_perm mf p22 0 40 Cur Freeable) by (keep_return_owned F22P FrameR).
 assert (Frame : lframe (gej_add_finite_return_frame pa pb pu pv ps pt p12 p22 bh bi) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameP|].
     intros bx pos (NA & NB & NU & NV & NS & NT & N12 & N22 & NH & NI) VB.
     unfold gej_add_finite_difference_frame,gej_add_preparation_frame;
       repeat split;try assumption;left;assumption.
   - eapply lframe_implies;[exact FrameR|].
     intros bx pos (NA & NB & NU & NV & NS & NT & N12 & N22 & NH & NI) VB;repeat split;assumption. }
 exists mf;split.
 - rewrite gej_add_finite_difference_body_source.
   eapply exec_statement_prefix_then_last;[exact Prepare|].
   rewrite gej_add_zero_head_source;eapply exec_Sseq_2;[exact Return|discriminate].
 - repeat (first [assumption|split]).
Qed.

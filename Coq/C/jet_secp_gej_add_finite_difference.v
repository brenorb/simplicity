(** Original finite prefix through the H/I differences, derived from the two
    original represented points and initially uninitialized private fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_field_mul_small
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix
 C.jet_secp_curve_statements C.jet_secp_gej_add_statements C.jet_secp_gej_add_preparation
 C.jet_secp_gej_add_finite_prepare C.jet_secp_mixed_difference.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Definition gej_add_u1_words x w := point_mul_words x (square_words w).
Definition gej_add_u2_words u z := point_mul_words u (square_words z).
Definition gej_add_s1_words y w := point_mul_words (point_mul_words y (square_words w)) w.
Definition gej_add_s2_words v z := point_mul_words (point_mul_words v (square_words z)) z.
Definition gej_add_h_words x z u w := mixed_difference_words (gej_add_u1_words x w) (gej_add_u2_words u z).
Definition gej_add_i_words y z v w := mixed_difference_words (gej_add_s2_words v z) (gej_add_s1_words y w).
Definition gej_add_finite_difference := statement_sequence (firstn 14 gej_add_statements) Sskip.
Definition gej_add_finite_difference_frame pa pb pu pv ps pt p12 p22 bh bi b pos :=
 b<>bh /\ b<>bi /\ gej_add_preparation_frame pa pb pu pv ps pt p12 p22 b pos.
Lemma gej_add_finite_difference_source : gej_add_finite_difference=
 statement_sequence (firstn 10 gej_add_statements) (statement_sequence mixed_difference_statements Sskip).
Proof. reflexivity. Qed.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with H : ~(?P \/ ?Q) |- _ =>
   let H1 := fresh "Sep" in let H2 := fresh "Sep" in
   assert (H1 : ~P) by (intro;apply H;left;assumption);
   assert (H2 : ~Q) by (intro;apply H;right;assumption);clear H end.
Local Ltac outside_prepare :=
 unfold gej_add_preparation_frame;repeat split;try (left;congruence);congruence.
Local Ltac outside_difference := repeat split;congruence.
Local Ltac keep_field HF Frame :=
 eapply field_at_lframe;[exact HF|exact Frame|];intro pos;outside_difference.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;outside_difference.

Theorem exec_gej_add_finite_difference e le m pa pb pu pv ps pt p12 p22 bh bi x y z u v w :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 e!_u1=Some (pu,curve_fe_type) -> e!_u2=Some (pv,curve_fe_type) ->
 e!_s1=Some (ps,curve_fe_type) -> e!_s2=Some (pt,curve_fe_type) ->
 e!_z12=Some (p12,curve_fe_type) -> e!_z22=Some (p22,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 NoDup [pa;pb;pu;pv;ps;pt;p12;p22;bh;bi] ->
 Mem.load Mint32 m pa 120=Some (Vint Int.zero) -> Mem.load Mint32 m pb 120=Some (Vint Int.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds w ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 0 (words5 u) -> fe_at m pb 40 (words5 v) -> fe_at m pb 80 (words5 w) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m gej_add_finite_difference E0 (gej_add_finite_prepare_temps le) mf Out_normal /\
 fe_at mf pa 0 (words5 x) /\ fe_at mf pa 40 (words5 y) /\ fe_at mf pa 80 (words5 z) /\
 fe_at mf pb 0 (words5 u) /\ fe_at mf pb 40 (words5 v) /\ fe_at mf pb 80 (words5 w) /\
 fe_at mf pu 0 (words5 (gej_add_u1_words x w)) /\ fe_at mf pv 0 (words5 (gej_add_u2_words u z)) /\
 fe_at mf ps 0 (words5 (gej_add_s1_words y w)) /\ fe_at mf pt 0 (words5 (gej_add_s2_words v z)) /\
 fe_at mf bh 0 (words5 (gej_add_h_words x z u w)) /\ fe_at mf bi 0 (words5 (gej_add_i_words y z v w)) /\
 Mem.load Mint32 mf pa 120=Some (Vint Int.zero) /\ Mem.load Mint32 mf pb 120=Some (Vint Int.zero) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\ Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\ Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\ Mem.range_perm mf p22 0 40 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 square_input_bounds (gej_add_h_words x z u w) /\ square_input_bounds (gej_add_i_words y z v w) /\
 mul_small_input_bounds (gej_add_u1_words x w) /\ mul_small_input_bounds (gej_add_u2_words u z) /\
 mul_small_input_bounds (gej_add_s1_words y w) /\ mul_small_input_bounds (gej_add_s2_words v z) /\
 lframe (gej_add_finite_difference_frame pa pb pu pv ps pt p12 p22 bh bi) m mf.
Proof.
 intros PA PB EU EV ES ET E12 E22 EH EI EQ EM EN EA Sep FlagA FlagB BX BY BZ BU BV BW
   AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI.
 pose proof Sep as Sep0;separate_blocks Sep0.
 assert (SepP : NoDup [pa;pb;pu;pv;ps;pt;p12;p22]).
 { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence. }
 assert (SepD : NoDup [bh;bi;pu;pv;ps;pt]).
 { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence. }
 destruct (exec_gej_add_finite_prepare e le m pa pb pu pv ps pt p12 p22 x y z u v w
   PA PB EU EV ES ET E12 E22 EQ EM SepP FlagA FlagB BX BY BZ BU BV BW AX AY AZ BXf BYf BZf
   FA FB FU FV FS FT F12 F22)
   as (mp & Prepare & AXP & AYP & AZP & BXP & BYP & BZP & UP & VP & SP & TP & Z12P & Z22P &
     FAP & FBP & FUP & FVP & FSP & FTP & F12P & F22P & TightU & TightV & TightS & TightT & FrameP).
 assert (FHP : Mem.range_perm mp bh 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FH|exact FrameP|];intro pos;outside_prepare. }
 assert (FIP : Mem.range_perm mp bi 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FI|exact FrameP|];intro pos;outside_prepare. }
 destruct (exec_mixed_differences e (gej_add_finite_prepare_temps le) mp bh bi pu pv ps pt
   (gej_add_u1_words x w) (gej_add_u2_words u z) (gej_add_s1_words y w) (gej_add_s2_words v z)
   EH EI EU EV ES ET EN EA SepD TightU TightV TightS TightT UP VP SP TP FHP FIP FUP FVP FSP FTP)
   as (mf & Differences & H & I & UF & VF & SF & TF & FHF & FIF & FUF & FVF & FSF & FTF &
     ValH & ValI & BoundH & BoundI & FrameD).
 assert (AXF : fe_at mf pa 0 (words5 x)) by (keep_field AXP FrameD).
 assert (AYF : fe_at mf pa 40 (words5 y)) by (keep_field AYP FrameD).
 assert (AZF : fe_at mf pa 80 (words5 z)) by (keep_field AZP FrameD).
 assert (BXF : fe_at mf pb 0 (words5 u)) by (keep_field BXP FrameD).
 assert (BYF : fe_at mf pb 40 (words5 v)) by (keep_field BYP FrameD).
 assert (BZF : fe_at mf pb 80 (words5 w)) by (keep_field BZP FrameD).
 assert (FAF : Mem.range_perm mf pa 0 128 Cur Freeable) by (keep_free FAP FrameD).
 assert (FBF : Mem.range_perm mf pb 0 128 Cur Freeable) by (keep_free FBP FrameD).
 assert (F12F : Mem.range_perm mf p12 0 40 Cur Freeable) by (keep_free F12P FrameD).
 assert (F22F : Mem.range_perm mf p22 0 40 Cur Freeable) by (keep_free F22P FrameD).
 assert (Frame : lframe (gej_add_finite_difference_frame pa pb pu pv ps pt p12 p22 bh bi) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameP|];intros b pos [NH [NI Rest]] VB;exact Rest.
   - eapply lframe_implies;[exact FrameD|].
     intros b pos (NH & NI & NU & NV & NS & NT & N12 & N22 & NP & NQ) VB;repeat split;assumption. }
 assert (FlagAF : Mem.load Mint32 mf pa 120=Some (Vint Int.zero)).
 { rewrite (proj1 Frame Mint32 pa 120);[exact FlagA| |].
   - eapply Mem.perm_valid_block;apply (FA 0);lia.
   - intros pos Pos;unfold gej_add_finite_difference_frame,gej_add_preparation_frame;
     repeat split;try (left;congruence);try congruence;right;right;change (120<=pos<124) in Pos;lia. }
 assert (FlagBF : Mem.load Mint32 mf pb 120=Some (Vint Int.zero)).
 { rewrite (proj1 Frame Mint32 pb 120);[exact FlagB| |].
   - eapply Mem.perm_valid_block;apply (FB 0);lia.
   - intros pos Pos;unfold gej_add_finite_difference_frame,gej_add_preparation_frame;
     repeat split;try (left;congruence);try congruence;right;right;change (120<=pos<124) in Pos;lia. }
 exists mf;split.
 - rewrite gej_add_finite_difference_source;eapply exec_statement_prefix_then_last;[exact Prepare|exact Differences].
 - split;[exact AXF|];split;[exact AYF|];split;[exact AZF|];split;[exact BXF|];split;[exact BYF|];split;[exact BZF|].
   split;[exact UF|];split;[exact VF|];split;[exact SF|];split;[exact TF|];split;[exact H|];split;[exact I|].
   split;[exact FlagAF|];split;[exact FlagBF|];split;[exact FAF|];split;[exact FBF|].
   split;[exact FUF|];split;[exact FVF|];split;[exact FSF|];split;[exact FTF|];split;[exact F12F|];split;[exact F22F|].
   split;[exact FHF|];split;[exact FIF|];split;[exact BoundH|];split;[exact BoundI|].
   split;[exact TightU|];split;[exact TightV|];split;[exact TightS|];split;[exact TightT|exact Frame].
Qed.

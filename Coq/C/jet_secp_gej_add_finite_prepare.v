(** Full original finite dispatch, both squares and six preparation products.
    The square factors and all intermediate execution are derived from inputs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
 C.jet_secp_field_mul_small C.jet_secp_curve_frame C.jet_secp_statement_prefix
 C.jet_secp_curve_statements C.jet_secp_gej_add_statements C.jet_secp_gej_add_finite_start
 C.jet_secp_gej_add_preparation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Definition gej_add_finite_prepare := statement_sequence (firstn 10 gej_add_statements) Sskip.
Definition gej_add_finite_prepare_temps le :=
 PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le).
Lemma gej_add_finite_prepare_source : gej_add_finite_prepare=
 statement_sequence (firstn 4 gej_add_statements)
   (statement_sequence gej_add_preparation_statements Sskip).
Proof. reflexivity. Qed.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with H : ~(?P \/ ?Q) |- _ =>
   let H1 := fresh "Sep" in let H2 := fresh "Sep" in
   assert (H1 : ~P) by tauto;assert (H2 : ~Q) by tauto;clear H end.
Local Ltac geometry arithmetic :=
 try unfold gej_add_squares_frame;
 lazymatch goal with
 | |- _ /\ _ => split;geometry arithmetic
 | |- _ <> _ => congruence
 | |- _ \/ _ => first [solve [left;congruence] | solve [right;left;arithmetic] | solve [right;right;arithmetic]]
 end.
Local Ltac keep_field HF Frame :=
 eapply curve_keep_field_range;[reflexivity|exact HF|exact Frame|];intros pos Pos;geometry ltac:(clear -Pos;lia).
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;geometry ltac:(fail "unexpected owner overlap").

Theorem exec_gej_add_finite_prepare e le m pa pb pu pv ps pt p12 p22 x y z u v w :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 e!_u1=Some (pu,curve_fe_type) -> e!_u2=Some (pv,curve_fe_type) ->
 e!_s1=Some (ps,curve_fe_type) -> e!_s2=Some (pt,curve_fe_type) ->
 e!_z12=Some (p12,curve_fe_type) -> e!_z22=Some (p22,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None ->
 NoDup [pa;pb;pu;pv;ps;pt;p12;p22] ->
 Mem.load Mint32 m pa 120=Some (Vint Int.zero) -> Mem.load Mint32 m pb 120=Some (Vint Int.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds w ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 0 (words5 u) -> fe_at m pb 40 (words5 v) -> fe_at m pb 80 (words5 w) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m gej_add_finite_prepare E0 (gej_add_finite_prepare_temps le) mf Out_normal /\
 fe_at mf pa 0 (words5 x) /\ fe_at mf pa 40 (words5 y) /\ fe_at mf pa 80 (words5 z) /\
 fe_at mf pb 0 (words5 u) /\ fe_at mf pb 40 (words5 v) /\ fe_at mf pb 80 (words5 w) /\
 fe_at mf pu 0 (words5 (point_mul_words x (square_words w))) /\ fe_at mf pv 0 (words5 (point_mul_words u (square_words z))) /\
 fe_at mf ps 0 (words5 (point_mul_words (point_mul_words y (square_words w)) w)) /\
 fe_at mf pt 0 (words5 (point_mul_words (point_mul_words v (square_words z)) z)) /\
 fe_at mf p12 0 (words5 (square_words z)) /\ fe_at mf p22 0 (words5 (square_words w)) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\ Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\ Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\ Mem.range_perm mf p22 0 40 Cur Freeable /\
 mul_small_input_bounds (point_mul_words x (square_words w)) /\ mul_small_input_bounds (point_mul_words u (square_words z)) /\
 mul_small_input_bounds (point_mul_words (point_mul_words y (square_words w)) w) /\
 mul_small_input_bounds (point_mul_words (point_mul_words v (square_words z)) z) /\
 lframe (gej_add_preparation_frame pa pb pu pv ps pt p12 p22) m mf.
Proof.
 intros PA PB EU EV ES ET E12 E22 EQ EM Sep FlagA FlagB BX BY BZ BU BV BW
   AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22.
 pose proof Sep as Sep0;separate_blocks Sep0.
 assert (SepZ : NoDup [pa;pb;p22;p12]).
 { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence. }
 destruct (exec_gej_add_finite_start e le m pa pb p22 p12 z w PA PB E22 E12 EQ SepZ
   FlagA FlagB BZ BW AZ BZf FA FB F22 F12)
   as (mi & Start & Z22 & Z12 & AZI & BZI & FAI & FBI & F22I & F12I & Bound12 & Bound22 & FrameS).
 assert (AXI : fe_at mi pa 0 (words5 x)) by (keep_field AX FrameS).
 assert (AYI : fe_at mi pa 40 (words5 y)) by (keep_field AY FrameS).
 assert (BXI : fe_at mi pb 0 (words5 u)) by (keep_field BXf FrameS).
 assert (BYI : fe_at mi pb 40 (words5 v)) by (keep_field BYf FrameS).
 assert (FUI : Mem.range_perm mi pu 0 40 Cur Freeable) by (keep_free FU FrameS).
 assert (FVI : Mem.range_perm mi pv 0 40 Cur Freeable) by (keep_free FV FrameS).
 assert (FSI : Mem.range_perm mi ps 0 40 Cur Freeable) by (keep_free FS FrameS).
 assert (FTI : Mem.range_perm mi pt 0 40 Cur Freeable) by (keep_free FT FrameS).
 set (lt := gej_add_finite_prepare_temps le).
 assert (PAT : lt!_a=Some (Vptr pa Ptrofs.zero)).
 { unfold lt,gej_add_finite_prepare_temps;rewrite !PTree.gso by discriminate;exact PA. }
 assert (PBT : lt!_b=Some (Vptr pb Ptrofs.zero)).
 { unfold lt,gej_add_finite_prepare_temps;rewrite !PTree.gso by discriminate;exact PB. }
 destruct (exec_gej_add_preparation e lt mi pa pb pu pv ps pt p12 p22 x y z u v w
   (square_words z) (square_words w) PAT PBT EU EV ES ET E12 E22 EM Sep
   BX BY BZ BU BV BW Bound12 Bound22 AXI AYI AZI BXI BYI BZI Z12 Z22
   FAI FBI FUI FVI FSI FTI F12I F22I)
   as (mf & Prepare & AXF & AYF & AZF & BXF & BYF & BZF & UF & VF & SF & TF & A12 & B22 &
     FAF & FBF & FUF & FVF & FSF & FTF & F12F & F22F & TightU & TightV & TightS & TightT & FrameP).
 assert (Frame : lframe (gej_add_preparation_frame pa pb pu pv ps pt p12 p22) m mf).
 { eapply lframe_trans;[|exact FrameP].
   eapply lframe_implies;[exact FrameS|].
   intros b pos (NU & NV & NS & NT & N12 & N22 & NP & NQ) VB.
   destruct NP as [NP|[NP|NP]];destruct NQ as [NQ|[NQ|NQ]];geometry ltac:(clear -NP NQ;lia). }
 exists mf;split.
 - rewrite gej_add_finite_prepare_source;eapply exec_statement_prefix_then_last;[exact Start|exact Prepare].
 - repeat (first [assumption|split]).
Qed.

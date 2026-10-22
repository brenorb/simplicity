(** Actual six-multiplication projective preparation, from owned point fields.
    No intermediate call, initialized temporary or arithmetic result is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_double_coordinate_numeric
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_curve_square
 C.jet_secp_curve_statements C.jet_secp_statement_prefix C.jet_secp_gej_fresh_product
 C.jet_secp_gej_add_statements C.jet_secp_gej_add_s_calls.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Definition gej_add_preparation_statements :=
 [gej_fresh_product_stmt false _u1 _a _z22;gej_fresh_product_stmt false _u2 _b _z12;
  gej_add_s_first false;gej_add_s_second false;gej_add_s_first true;gej_add_s_second true].
Definition gej_add_preparation_frame (pa pb pu pv ps pt p12 p22 b : block) (pos : Z) :=
 b<>pu /\ b<>pv /\ b<>ps /\ b<>pt /\ b<>p12 /\ b<>p22 /\
 (b<>pa \/ pos<0 \/ 120<=pos) /\ (b<>pb \/ pos<0 \/ 120<=pos).
Lemma gej_add_preparation_source : gej_add_after 4=
 statement_sequence gej_add_preparation_statements (gej_add_after 10).
Proof. reflexivity. Qed.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with H : ~(?P \/ ?Q) |- _ =>
   let H1 := fresh "Sep" in let H2 := fresh "Sep" in
   assert (H1 : ~P) by tauto;assert (H2 : ~Q) by tauto;clear H end.
Local Ltac geometry arithmetic :=
 cbn [curve_square_offset];try unfold gej_add_s_frame;
 lazymatch goal with
 | |- _ /\ _ => split;geometry arithmetic
 | |- _ <> _ => congruence
 | |- _ \/ _ => first [solve [left;congruence] | solve [right;left;arithmetic] | solve [right;right;arithmetic]]
 end.
Local Ltac keep_field HF Frame :=
 eapply curve_keep_field_range;[reflexivity|exact HF|exact Frame|];intros pos Pos;geometry ltac:(clear -Pos;lia).
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;geometry ltac:(fail "unexpected input-owner overlap").

Theorem exec_gej_add_preparation e le m pa pb pu pv ps pt p12 p22 x y z u v w a b :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 e!_u1=Some (pu,curve_fe_type) -> e!_u2=Some (pv,curve_fe_type) ->
 e!_s1=Some (ps,curve_fe_type) -> e!_s2=Some (pt,curve_fe_type) ->
 e!_z12=Some (p12,curve_fe_type) -> e!_z22=Some (p22,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 NoDup [pa;pb;pu;pv;ps;pt;p12;p22] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds w ->
 square_input_bounds a -> square_input_bounds b ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 0 (words5 u) -> fe_at m pb 40 (words5 v) -> fe_at m pb 80 (words5 w) ->
 fe_at m p12 0 (words5 a) -> fe_at m p22 0 (words5 b) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence gej_add_preparation_statements Sskip) E0 le mf Out_normal /\
 fe_at mf pa 0 (words5 x) /\ fe_at mf pa 40 (words5 y) /\ fe_at mf pa 80 (words5 z) /\
 fe_at mf pb 0 (words5 u) /\ fe_at mf pb 40 (words5 v) /\ fe_at mf pb 80 (words5 w) /\
 fe_at mf pu 0 (words5 (point_mul_words x b)) /\ fe_at mf pv 0 (words5 (point_mul_words u a)) /\
 fe_at mf ps 0 (words5 (point_mul_words (point_mul_words y b) w)) /\
 fe_at mf pt 0 (words5 (point_mul_words (point_mul_words v a) z)) /\
 fe_at mf p12 0 (words5 a) /\ fe_at mf p22 0 (words5 b) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\ Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\ Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\ Mem.range_perm mf p22 0 40 Cur Freeable /\
 mul_small_input_bounds (point_mul_words x b) /\ mul_small_input_bounds (point_mul_words u a) /\
 mul_small_input_bounds (point_mul_words (point_mul_words y b) w) /\
 mul_small_input_bounds (point_mul_words (point_mul_words v a) z) /\
 lframe (gej_add_preparation_frame pa pb pu pv ps pt p12 p22) m mf.
Proof.
 intros PA PB EU EV ES ET E12 E22 EM Sep BX BY BZ BU BV BW BA BB
   AX AY AZ BXf BYf BZf A B FA FB FU FV FS FT F12 F22.
 separate_blocks Sep.
 destruct (exec_gej_fresh_product false _u1 _a _z22 x b e le m pu pa p22
   EU PA E22 EM BX BB ltac:(congruence) ltac:(congruence) ltac:(congruence) FU AX FA B F22)
   as (m1 & C1 & U1 & AX1 & B1 & FU1 & FA1 & F221 & ValU & BoundU & Frame1).
 assert (AY1 : fe_at m1 pa 40 (words5 y)) by (keep_field AY Frame1).
 assert (AZ1 : fe_at m1 pa 80 (words5 z)) by (keep_field AZ Frame1).
 assert (BXf1 : fe_at m1 pb 0 (words5 u)) by (keep_field BXf Frame1).
 assert (BYf1 : fe_at m1 pb 40 (words5 v)) by (keep_field BYf Frame1).
 assert (BZf1 : fe_at m1 pb 80 (words5 w)) by (keep_field BZf Frame1).
 assert (A1 : fe_at m1 p12 0 (words5 a)) by (keep_field A Frame1).
 assert (FB1 : Mem.range_perm m1 pb 0 128 Cur Freeable) by (keep_free FB Frame1).
 assert (FV1 : Mem.range_perm m1 pv 0 40 Cur Freeable) by (keep_free FV Frame1).
 assert (FS1 : Mem.range_perm m1 ps 0 40 Cur Freeable) by (keep_free FS Frame1).
 assert (FT1 : Mem.range_perm m1 pt 0 40 Cur Freeable) by (keep_free FT Frame1).
 assert (F121 : Mem.range_perm m1 p12 0 40 Cur Freeable) by (keep_free F12 Frame1).
 destruct (exec_gej_fresh_product false _u2 _b _z12 u a e le m1 pv pb p12
   EV PB E12 EM BU BA ltac:(congruence) ltac:(congruence) ltac:(congruence) FV1 BXf1 FB1 A1 F121)
   as (m2 & C2 & V2 & BXf2 & A2 & FV2 & FB2 & F122 & ValV & BoundV & Frame2).
 assert (AX2 : fe_at m2 pa 0 (words5 x)) by (keep_field AX1 Frame2).
 assert (AY2 : fe_at m2 pa 40 (words5 y)) by (keep_field AY1 Frame2).
 assert (AZ2 : fe_at m2 pa 80 (words5 z)) by (keep_field AZ1 Frame2).
 assert (BYf2 : fe_at m2 pb 40 (words5 v)) by (keep_field BYf1 Frame2).
 assert (BZf2 : fe_at m2 pb 80 (words5 w)) by (keep_field BZf1 Frame2).
 assert (U2 : fe_at m2 pu 0 (words5 (point_mul_words x b))) by (keep_field U1 Frame2).
 assert (B2 : fe_at m2 p22 0 (words5 b)) by (keep_field B1 Frame2).
 assert (FA2 : Mem.range_perm m2 pa 0 128 Cur Freeable) by (keep_free FA1 Frame2).
 assert (FU2 : Mem.range_perm m2 pu 0 40 Cur Freeable) by (keep_free FU1 Frame2).
 assert (FS2 : Mem.range_perm m2 ps 0 40 Cur Freeable) by (keep_free FS1 Frame2).
 assert (FT2 : Mem.range_perm m2 pt 0 40 Cur Freeable) by (keep_free FT1 Frame2).
 assert (F222 : Mem.range_perm m2 p22 0 40 Cur Freeable) by (keep_free F221 Frame2).
 destruct (exec_gej_add_s_calls false e le m2 pa pb ps p22 y b w
   PA PB ES E22 EM ltac:(congruence) ltac:(congruence) ltac:(congruence)
   ltac:(congruence) ltac:(congruence) ltac:(congruence) BY BB BW AY2 B2 BZf2 FA2 FB2 FS2 F222)
   as (m3 & m4 & C3 & C4 & S4 & AY4 & B4 & BZf4 & FA4 & FB4 & FS4 & F224 & ValS & BoundS & TightS & FrameS).
 assert (AX4 : fe_at m4 pa 0 (words5 x)) by (keep_field AX2 FrameS).
 assert (AZ4 : fe_at m4 pa 80 (words5 z)) by (keep_field AZ2 FrameS).
 assert (BXf4 : fe_at m4 pb 0 (words5 u)) by (keep_field BXf2 FrameS).
 assert (BYf4 : fe_at m4 pb 40 (words5 v)) by (keep_field BYf2 FrameS).
 assert (U4 : fe_at m4 pu 0 (words5 (point_mul_words x b))) by (keep_field U2 FrameS).
 assert (V4 : fe_at m4 pv 0 (words5 (point_mul_words u a))) by (keep_field V2 FrameS).
 assert (A4 : fe_at m4 p12 0 (words5 a)) by (keep_field A2 FrameS).
 assert (FU4 : Mem.range_perm m4 pu 0 40 Cur Freeable) by (keep_free FU2 FrameS).
 assert (FV4 : Mem.range_perm m4 pv 0 40 Cur Freeable) by (keep_free FV2 FrameS).
 assert (FT4 : Mem.range_perm m4 pt 0 40 Cur Freeable) by (keep_free FT2 FrameS).
 assert (F124 : Mem.range_perm m4 p12 0 40 Cur Freeable) by (keep_free F122 FrameS).
 destruct (exec_gej_add_s_calls true e le m4 pb pa pt p12 v a z
   PB PA ET E12 EM ltac:(congruence) ltac:(congruence) ltac:(congruence)
   ltac:(congruence) ltac:(congruence) ltac:(congruence) BV BA BZ BYf4 A4 AZ4 FB4 FA4 FT4 F124)
   as (m5 & m6 & C5 & C6 & T6 & BYf6 & A6 & AZ6 & FB6 & FA6 & FT6 & F126 & ValT & BoundT & TightT & FrameT).
 assert (AX6 : fe_at m6 pa 0 (words5 x)) by (keep_field AX4 FrameT).
 assert (AY6 : fe_at m6 pa 40 (words5 y)) by (keep_field AY4 FrameT).
 assert (BXf6 : fe_at m6 pb 0 (words5 u)) by (keep_field BXf4 FrameT).
 assert (BZf6 : fe_at m6 pb 80 (words5 w)) by (keep_field BZf4 FrameT).
 assert (U6 : fe_at m6 pu 0 (words5 (point_mul_words x b))) by (keep_field U4 FrameT).
 assert (V6 : fe_at m6 pv 0 (words5 (point_mul_words u a))) by (keep_field V4 FrameT).
 assert (S6 : fe_at m6 ps 0 (words5 (point_mul_words (point_mul_words y b) w))) by (keep_field S4 FrameT).
 assert (B6 : fe_at m6 p22 0 (words5 b)) by (keep_field B4 FrameT).
 assert (FU6 : Mem.range_perm m6 pu 0 40 Cur Freeable) by (keep_free FU4 FrameT).
 assert (FV6 : Mem.range_perm m6 pv 0 40 Cur Freeable) by (keep_free FV4 FrameT).
 assert (FS6 : Mem.range_perm m6 ps 0 40 Cur Freeable) by (keep_free FS4 FrameT).
 assert (F226 : Mem.range_perm m6 p22 0 40 Cur Freeable) by (keep_free F224 FrameT).
 assert (TightU : mul_small_input_bounds (point_mul_words x b)) by (apply double_mul_tight;assumption).
 assert (TightV : mul_small_input_bounds (point_mul_words u a)) by (apply double_mul_tight;assumption).
 exists m6;split.
 - unfold gej_add_preparation_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);[exact C1|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[exact C2|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);[exact C3|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le);[exact C4|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m5) (le1:=le);[exact C5|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m6) (le1:=le);[exact C6|apply exec_Sskip].
 - split;[exact AX6|];split;[exact AY6|];split;[exact AZ6|];split;[exact BXf6|];split;[exact BYf6|];split;[exact BZf6|].
   split;[exact U6|];split;[exact V6|];split;[exact S6|];split;[exact T6|];split;[exact A6|];split;[exact B6|].
   split;[exact FA6|];split;[exact FB6|];split;[exact FU6|];split;[exact FV6|];split;[exact FS6|];split;[exact FT6|];split;[exact F126|];split;[exact F226|].
   split;[exact TightU|];split;[exact TightV|];split;[exact TightS|];split;[exact TightT|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact Frame1|].
     intros bx pos (NU & NV & NS & NT & N12 & N22 & NP & NQ) VB.
     destruct NP as [NP|[NP|NP]];destruct NQ as [NQ|[NQ|NQ]];geometry ltac:(clear -NP NQ;lia).
   + eapply lframe_trans.
     * eapply lframe_implies;[exact Frame2|].
       intros bx pos (NU & NV & NS & NT & N12 & N22 & NP & NQ) VB.
       destruct NP as [NP|[NP|NP]];destruct NQ as [NQ|[NQ|NQ]];geometry ltac:(clear -NP NQ;lia).
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameS|].
          intros bx pos (NU & NV & NS & NT & N12 & N22 & NP & NQ) VB.
          destruct NP as [NP|[NP|NP]];destruct NQ as [NQ|[NQ|NQ]];geometry ltac:(clear -NP NQ;lia).
       -- eapply lframe_implies;[exact FrameT|].
          intros bx pos (NU & NV & NS & NT & N12 & N22 & NP & NQ) VB.
          destruct NP as [NP|[NP|NP]];destruct NQ as [NQ|[NQ|NQ]];geometry ltac:(clear -NP NQ;lia).
Qed.

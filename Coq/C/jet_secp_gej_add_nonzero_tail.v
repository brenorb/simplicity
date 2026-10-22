(** Entire actual projective H-nonzero tail. Reuse the mixed H2/H3/T and X/Y
    statements only after executing the original, different projective Z prefix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_field_sum_bounds C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix
 C.jet_secp_gej_add_statements C.jet_secp_gej_add_nonzero_start C.jet_secp_field_mul_small
 C.jet_secp_field_negate_separate C.jet_secp_double_coordinate_numeric C.jet_secp_mixed_difference
 C.jet_secp_mixed_products C.jet_secp_mixed_nonzero_products C.jet_secp_mixed_nonzero_tail
 C.jet_secp_mixed_x_tail C.jet_secp_mixed_y_tail.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words negate_sep_words.

Definition gej_add_nonzero_tail_frame (pa pb bh b2 b3 bt bu bi bs bx : block) (_ : Z) :=
 bx<>pa /\ bx<>pb /\ bx<>bh /\ bx<>b2 /\ bx<>b3 /\ bx<>bt /\ bx<>bu /\ bx<>bi /\ bx<>bs.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_field HF Frame :=
 eapply field_at_lframe;[exact HF|exact Frame|];intro pos;
   unfold gej_add_nonzero_start_frame,mixed_product_frame;
   repeat split;try (left;congruence);congruence.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;
   unfold gej_add_nonzero_start_frame,mixed_product_frame,mixed_xy_frame;
   repeat split;try (left;congruence);congruence.

Theorem exec_gej_add_nonzero_tail e le m pa pb bh b2 b3 bt bu bi bs x y z w h u i s :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 le!_r=Some (Vptr pa Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
 e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> NoDup [pa;pb;bh;b2;b3;bt;bu;bi;bs] ->
 square_input_bounds z -> square_input_bounds w -> square_input_bounds h -> square_input_bounds u ->
 square_input_bounds i -> square_input_bounds s -> radix_value h mod feP<>0 ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) -> fe_at m pb 80 (words5 w) ->
 fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) -> fe_at m bi 0 (words5 i) -> fe_at m bs 0 (words5 s) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
 Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (gej_add_after 14) E0 (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
 fe_at mf pa 0 (words5 (mixed_nonzero_x_words h i u)) /\
 fe_at mf pa 40 (words5 (mixed_nonzero_y_words h i u s)) /\
 fe_at mf pa 80 (words5 (point_mul_words z (point_mul_words h w))) /\ Mem.load Mint32 mf pa 120=Some (Vint Int.zero) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
 Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
 Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
 square_input_bounds (mixed_nonzero_x_words h i u) /\ square_input_bounds (mixed_nonzero_y_words h i u s) /\
 square_input_bounds (point_mul_words z (point_mul_words h w)) /\
 lframe (gej_add_nonzero_tail_frame pa pb bh b2 b3 bt bu bi bs) m mf.
Proof.
 intros PA PB PR PN EH E2 E3 ET EU EI ES EN EM EQ EG EA Sep BZ BW BH BU BI BS HNZ X Y Z W H U I S FA FB FH F2 F3 FT FU FI FS.
 separate_blocks Sep.
 assert (SepZ : NoDup [pa;pb;bh;bt;b2]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence).
 assert (SepM : NoDup [b2;b3;bt;bh;bu]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence).
 assert (SepXY : NoDup [pa;bt;bi;b3;bs]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence).
 destruct (exec_gej_add_nonzero_prefix e le m pa pb bh bt b2 x y z w h
   PA PB PR PN EH ET E2 EN EM EQ SepZ BZ BW BH HNZ X Y Z W H FA FB FH FT F2)
   as (mz & Prefix & XZ & YZ & ZZ & FlagZ & WZ & HZ & TZ & H2Z &
     FAZ & FBZ & FHZ & FTZ & F2Z & BoundZ & BoundH2 & FrameZ).
 assert (UZ : fe_at mz bu 0 (words5 u)) by (keep_field U FrameZ).
 assert (IZ : fe_at mz bi 0 (words5 i)) by (keep_field I FrameZ).
 assert (SZ : fe_at mz bs 0 (words5 s)) by (keep_field S FrameZ).
 assert (F3Z : Mem.range_perm mz b3 0 40 Cur Freeable) by (keep_free F3 FrameZ).
 assert (FUZ : Mem.range_perm mz bu 0 40 Cur Freeable) by (keep_free FU FrameZ).
 assert (FIZ : Mem.range_perm mz bi 0 40 Cur Freeable) by (keep_free FI FrameZ).
 assert (FSZ : Mem.range_perm mz bs 0 40 Cur Freeable) by (keep_free FS FrameZ).
 destruct (exec_mixed_products e (PTree.set _t'2 (Vint Int.zero) le) mz b2 b3 bt bh bu (square_words h) h u
   E2 E3 ET EH EU EG EM SepM (double_square_tight h BH) BH BU H2Z HZ UZ F2Z F3Z FTZ FHZ FUZ)
   as (mp & Products & H2P & H3P & TP & HP & UP & F2P & F3P & FTP & FHP & FUP &
     ValH2 & BoundN & ValH3 & ValT & BoundH3 & BoundT & FrameP).
 assert (IP : fe_at mp bi 0 (words5 i)) by (keep_field IZ FrameP).
 assert (SP : fe_at mp bs 0 (words5 s)) by (keep_field SZ FrameP).
 assert (ZP : fe_at mp pa 80 (words5 (point_mul_words z (point_mul_words h w)))) by (keep_field ZZ FrameP).
 assert (FAP : Mem.range_perm mp pa 0 128 Cur Freeable) by (keep_free FAZ FrameP).
 assert (FBP : Mem.range_perm mp pb 0 128 Cur Freeable) by (keep_free FBZ FrameP).
 assert (FIP : Mem.range_perm mp bi 0 40 Cur Freeable) by (keep_free FIZ FrameP).
 assert (FSP : Mem.range_perm mp bs 0 40 Cur Freeable) by (keep_free FSZ FrameP).
 assert (FlagP : Mem.load Mint32 mp pa 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameP Mint32 pa 120);[exact FlagZ| |intros pos Pos;unfold mixed_product_frame;repeat split;congruence].
   eapply Mem.perm_valid_block;apply (FAZ 0);lia. }
 assert (PRP : (PTree.set _t'2 (Vint Int.zero) le)!_r=Some (Vptr pa Ptrofs.zero))
   by (rewrite PTree.gso by discriminate;exact PR).
 destruct (exec_mixed_xy_tail e (PTree.set _t'2 (Vint Int.zero) le) mp pa bi b3 bt bs
   i (mixed_h3_words h) (mixed_t_words u h) s PRP EI E3 ET ES EQ EM EA SepXY
   BI BoundH3 BoundT BS IP H3P TP SP FAP FIP F3P FTP FSP)
   as (mf & XY & XO & YO & TO & GO & IO & SO & FAO & FIO & F3O & FTO & FSO & BoundX & BoundY & BoundTX & FrameXY).
 assert (FBO : Mem.range_perm mf pb 0 128 Cur Freeable) by (keep_free FBP FrameXY).
 assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_free FHP FrameXY).
 assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2P FrameXY).
 assert (FUO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_free FUP FrameXY).
 assert (ZO : fe_at mf pa 80 (words5 (point_mul_words z (point_mul_words h w)))).
 { eapply curve_keep_field_range;[reflexivity|exact ZP|exact FrameXY|].
   intros pos Pos;unfold mixed_xy_frame;repeat split;try congruence;right;right;lia. }
 assert (FlagO : Mem.load Mint32 mf pa 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameXY Mint32 pa 120);[exact FlagP| |].
   - eapply Mem.perm_valid_block;apply (FAP 0);lia.
   - intros pos Pos;unfold mixed_xy_frame;repeat split;try congruence;right;right;
       change (120<=pos<124) in Pos;lia. }
 assert (BoundXO : square_input_bounds (mixed_nonzero_x_words h i u))
   by (exact (field_scaled_loose 4 _ ltac:(lia) BoundX)).
 assert (BoundYO : square_input_bounds (mixed_nonzero_y_words h i u s))
   by (exact (field_scaled_loose 2 _ ltac:(lia) BoundY)).
 assert (Frame : lframe (gej_add_nonzero_tail_frame pa pb bh b2 b3 bt bu bi bs) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameZ|].
     intros bx pos (NA & NB & NH & N2 & N3 & NT & NU & NI & NS) VB;
       unfold gej_add_nonzero_start_frame;repeat split;assumption.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameP|].
       intros bx pos (NA & NB & NH & N2 & N3 & NT & NU & NI & NS) VB;
         unfold mixed_product_frame;repeat split;assumption.
     + eapply lframe_implies;[exact FrameXY|].
       intros bx pos (NA & NB & NH & N2 & N3 & NT & NU & NI & NS) VB;
         unfold mixed_xy_frame;repeat split;try assumption;left;exact NA. }
 exists mf;split.
 - rewrite gej_add_nonzero_prefix_source;eapply exec_statement_prefix_then_last;[exact Prefix|].
   rewrite gej_add_products_shared;eapply exec_statement_prefix_then_last;[exact Products|].
   rewrite gej_add_xy_tail_shared;exact XY.
 - repeat (first [assumption|split]).
Qed.

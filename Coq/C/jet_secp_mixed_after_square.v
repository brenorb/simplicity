(** Shared original continuation after H has been squared: products and X/Y. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_field_mul_small C.jet_secp_field_sum_bounds
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_statement_prefix C.jet_secp_mixed_nonzero_start C.jet_secp_mixed_products
 C.jet_secp_mixed_nonzero_products C.jet_secp_mixed_x_tail C.jet_secp_mixed_y_tail
 C.jet_secp_mixed_nonzero_tail C.jet_secp_double_coordinate_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.
Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.
Local Ltac keep_owned HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.

Theorem exec_mixed_after_h_square e le m bp bh b2 b3 bt bu bi bs w h u i s :
 le!_r=Some (Vptr bp Ptrofs.zero) ->
 e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
 e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 NoDup [bp;bh;b2;b3;bt;bu;bi;bs] ->
 square_input_bounds h -> square_input_bounds u -> square_input_bounds i -> square_input_bounds s ->
 fe_at m bp 80 (words5 w) -> Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bh 0 (words5 h) -> fe_at m b2 0 (words5 (square_words h)) ->
 fe_at m bu 0 (words5 u) -> fe_at m bi 0 (words5 i) -> fe_at m bs 0 (words5 s) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
 Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m mixed_after_h_square E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 (mixed_nonzero_x_words h i u)) /\
 fe_at mf bp 40 (words5 (mixed_nonzero_y_words h i u s)) /\
 fe_at mf bp 80 (words5 w) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
 Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
 square_input_bounds (mixed_nonzero_x_words h i u) /\ square_input_bounds (mixed_nonzero_y_words h i u s) /\
 lframe (mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs) m mf.
Proof.
 intros HR EH E2 E3 ET EU EI ES EM EQ EN EA Sep BH BU BI BS ZAt Flag H H2 U I S PF FH F2 F3 FT FU IF SF.
 separate_blocks Sep.
 assert (SepP : NoDup [b2;b3;bt;bh;bu]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 assert (SepXY : NoDup [bp;bt;bi;b3;bs]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 destruct (exec_mixed_products e le m b2 b3 bt bh bu (square_words h) h u
   E2 E3 ET EH EU EN EM SepP (double_square_tight h BH) BH BU H2 H U F2 F3 FT FH FU)
   as (mp & Products & H2P & H3P & TP & HP & UP & F2P & F3P & FTP & FHP & FUP &
     ValN & BoundN & Val3 & ValT & Bound3 & BoundT & FP).
 assert (IP : fe_at mp bi 0 (words5 i)).
 { eapply field_at_lframe;[exact I|exact FP|];intro pos;unfold mixed_product_frame;repeat split;congruence. }
 assert (SP : fe_at mp bs 0 (words5 s)).
 { eapply field_at_lframe;[exact S|exact FP|];intro pos;unfold mixed_product_frame;repeat split;congruence. }
 assert (ZP : fe_at mp bp 80 (words5 w)).
 { eapply field_at_lframe;[exact ZAt|exact FP|];intro pos;unfold mixed_product_frame;repeat split;congruence. }
 assert (PFP : Mem.range_perm mp bp 0 128 Cur Freeable) by (keep_owned PF FP).
 assert (IFP : Mem.range_perm mp bi 0 40 Cur Freeable) by (keep_owned IF FP).
 assert (SFP : Mem.range_perm mp bs 0 40 Cur Freeable) by (keep_owned SF FP).
 assert (FlagP : Mem.load Mint32 mp bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FP Mint32 bp 120);[exact Flag| |intros pos Range;unfold mixed_product_frame;repeat split;congruence].
   eapply Mem.perm_valid_block;apply (PF 0);lia. }
 destruct (exec_mixed_xy_tail e le mp bp bi b3 bt bs i (mixed_h3_words h) (mixed_t_words u h) s
   HR EI E3 ET ES EQ EM EA SepXY BI Bound3 BoundT BS IP H3P TP SP PFP IFP F3P FTP SFP)
   as (mf & XY & XO & YO & TO & GO & IO & SO & PFO & IFO & F3O & FTO & SFO & BoundX & BoundY & BoundTX & FX).
 assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_owned FHP FX).
 assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_owned F2P FX).
 assert (FUO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_owned FUP FX).
 assert (ZO : fe_at mf bp 80 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact ZP|exact FX|].
   intros pos Range;unfold mixed_xy_frame;repeat split;try congruence;right;right;clear - Range;lia. }
 assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FX Mint32 bp 120);[exact FlagP| |].
   - eapply Mem.perm_valid_block;apply (PFP 0);lia.
   - intros pos Range;unfold mixed_xy_frame;repeat split;try congruence;right;right;
       change (120<=pos<124) in Range;clear - Range;lia. }
 assert (BX : square_input_bounds (mixed_nonzero_x_words h i u))
   by (exact (field_scaled_loose 4 _ ltac:(lia) BoundX)).
 assert (BY : square_input_bounds (mixed_nonzero_y_words h i u s))
   by (exact (field_scaled_loose 2 _ ltac:(lia) BoundY)).
 assert (Frame : lframe (mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FP|];intros bx pos (NH & N2 & N3 & NT & NU & NI & NS & NP) Valid.
     unfold mixed_product_frame;repeat split;assumption.
   - eapply lframe_implies;[exact FX|];intros bx pos (NH & N2 & N3 & NT & NU & NI & NS & NP) Valid.
     unfold mixed_xy_frame;split;[exact NI|];split;[exact N3|];split;[exact NT|];split;[exact NS|].
     destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;exact NP|right;right;clear - NP;lia]. }
 exists mf;split.
 - rewrite mixed_products_source;eapply exec_statement_prefix_then_last;[exact Products|exact XY].
 - repeat first [assumption|split].
Qed.

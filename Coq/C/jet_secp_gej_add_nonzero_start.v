(** Original finite nonzero-H Z prefix, including the distinct Bz factor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_double_statements C.jet_secp_double_flag
 C.jet_secp_double_var_owned C.jet_secp_double_var_statements C.jet_secp_double_coordinate_numeric
 C.jet_secp_point_mul_numeric C.jet_secp_point_mul_preservation C.jet_secp_point_write_run
 C.jet_secp_square_separate_caller C.jet_secp_statement_prefix C.jet_secp_gej_add_statements
 C.jet_secp_mixed_nonzero_start C.jet_secp_mixed_zero C.jet_secp_gej_z_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.

Definition gej_add_t_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _t;curve_local_address _h;double_point_address _b _z].
Definition gej_add_null_ratio := Sifthenelse double_var_null_test
 (Sassign (Ederef (Etempvar _rzr (tptr curve_fe_type)) curve_fe_type) (Evar _t curve_fe_type)) Sskip.
Definition gej_add_z_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [double_point_address _r _z;double_point_address _a _z;curve_local_address _t].
Definition gej_add_nonzero_start_statements :=
 [mixed_clear_flag;gej_add_t_mul;gej_add_null_ratio;gej_add_z_mul;mixed_h_square].
Definition gej_add_nonzero_start_frame (pa pb bh bt b2 bx : block) (_ : Z) :=
 bx<>pa /\ bx<>pb /\ bx<>bh /\ bx<>bt /\ bx<>b2.
Lemma gej_add_nonzero_start_source : gej_add_after 15=
 statement_sequence gej_add_nonzero_start_statements (gej_add_after 20).
Proof. reflexivity. Qed.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_field HF Frame :=
 eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_gej_add_nonzero_start e le m pa pb bh bt b2 x y z w h :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 le!_r=Some (Vptr pa Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 e!_h=Some (bh,curve_fe_type) -> e!_t=Some (bt,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> NoDup [pa;pb;bh;bt;b2] ->
 square_input_bounds z -> square_input_bounds w -> square_input_bounds h ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 80 (words5 w) -> fe_at m bh 0 (words5 h) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence gej_add_nonzero_start_statements Sskip) E0 le mf Out_normal /\
 fe_at mf pa 0 (words5 x) /\ fe_at mf pa 40 (words5 y) /\
 fe_at mf pa 80 (words5 (point_mul_words z (point_mul_words h w))) /\
 Mem.load Mint32 mf pa 120=Some (Vint Int.zero) /\
 fe_at mf pb 80 (words5 w) /\ fe_at mf bh 0 (words5 h) /\
 fe_at mf bt 0 (words5 (point_mul_words h w)) /\ fe_at mf b2 0 (words5 (square_words h)) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
 square_input_bounds (point_mul_words z (point_mul_words h w)) /\
 square_input_bounds (square_words h) /\
 lframe (gej_add_nonzero_start_frame pa pb bh bt b2) m mf.
Proof.
 intros PA PB PR PN EH ET E2 EM EQ Sep BZ BW BH X Y Z W H FA FB FH FT F2.
 separate_blocks Sep.
 destruct (double_var_store_flag x y z m pa Int.zero X Y Z FA)
   as (m0 & Store & Flag0 & X0 & Y0 & Z0 & FA0 & Frame0).
 assert (H0 : fe_at m0 bh 0 (words5 h)) by (keep_field H Frame0).
 assert (W0 : fe_at m0 pb 80 (words5 w)) by (keep_field W Frame0).
 assert (FH0 : Mem.range_perm m0 bh 0 40 Cur Freeable) by (keep_free FH Frame0).
 assert (FB0 : Mem.range_perm m0 pb 0 128 Cur Freeable) by (keep_free FB Frame0).
 assert (FT0 : Mem.range_perm m0 bt 0 40 Cur Freeable) by (keep_free FT Frame0).
 assert (F20 : Mem.range_perm m0 b2 0 40 Cur Freeable) by (keep_free F2 Frame0).
 destruct (eval_gej_z_product_owned h w m0 bt bh pb BH BW ltac:(congruence) ltac:(congruence) ltac:(congruence)
   FT0 H0 FH0 W0 FB0)
   as (mt & CT & T1 & H1 & W1 & FT1 & FH1 & FB1 & ValT & BoundT & FrameT).
 assert (X1 : fe_at mt pa 0 (words5 x)) by (keep_field X0 FrameT).
 assert (Y1 : fe_at mt pa 40 (words5 y)) by (keep_field Y0 FrameT).
 assert (Z1 : fe_at mt pa 80 (words5 z)) by (keep_field Z0 FrameT).
 assert (FA1 : Mem.range_perm mt pa 0 128 Cur Freeable) by (keep_free FA0 FrameT).
 assert (F21 : Mem.range_perm mt b2 0 40 Cur Freeable) by (keep_free F20 FrameT).
 assert (Flag1 : Mem.load Mint32 mt pa 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameT Mint32 pa 120);[exact Flag0| |intros pos Pos;repeat split;try (left;congruence);congruence].
   eapply Mem.perm_valid_block;apply (FA0 0);lia. }
 destruct (eval_point_mul_numeric PointZ z (point_mul_words h w) mt pa bt BZ (double_tight_loose _ BoundT)
   ltac:(congruence) Z1 FA1 T1 FT1)
   as (mz & CZ & Z2 & FA2 & T2 & FT2 & ValZ & BoundZ & RawFrameZ).
 pose proof (point_mul_external_frame PointZ mt mz pa bt RawFrameZ) as FrameZ.
 assert (X2 : fe_at mz pa 0 (words5 x)).
 { exact (point_mul_other_field PointZ PointX mt mz pa bt x ltac:(discriminate) ltac:(congruence) X1 FA2 RawFrameZ). }
 assert (Y2 : fe_at mz pa 40 (words5 y)).
 { exact (point_mul_other_field PointZ PointY mt mz pa bt y ltac:(discriminate) ltac:(congruence) Y1 FA2 RawFrameZ). }
 assert (H2 : fe_at mz bh 0 (words5 h)) by (keep_field H1 FrameZ).
 assert (W2 : fe_at mz pb 80 (words5 w)) by (keep_field W1 FrameZ).
 assert (FH2 : Mem.range_perm mz bh 0 40 Cur Freeable) by (keep_free FH1 FrameZ).
 assert (FB2 : Mem.range_perm mz pb 0 128 Cur Freeable) by (keep_free FB1 FrameZ).
 assert (F22 : Mem.range_perm mz b2 0 40 Cur Freeable) by (keep_free F21 FrameZ).
 assert (Flag2 : Mem.load Mint32 mz pa 120=Some (Vint Int.zero)).
 { eapply (point_mul_flag PointZ mt mz pa bt Int.zero);[congruence| |exact Flag1|exact RawFrameZ].
   eapply Mem.perm_valid_block;apply (FA1 0);lia. }
 destruct (eval_square_separate_from_storage h mz b2 bh BH F22 H2 FH2 ltac:(congruence))
   as (mf & CS & H2O & F2O & HO & FHO & ValH & BoundH & FrameS).
 assert (XO : fe_at mf pa 0 (words5 x)) by (keep_field X2 FrameS).
 assert (YO : fe_at mf pa 40 (words5 y)) by (keep_field Y2 FrameS).
 assert (ZO : fe_at mf pa 80 (words5 (point_mul_words z (point_mul_words h w)))) by (keep_field Z2 FrameS).
 assert (WO : fe_at mf pb 80 (words5 w)) by (keep_field W2 FrameS).
 assert (TO : fe_at mf bt 0 (words5 (point_mul_words h w))) by (keep_field T2 FrameS).
 assert (FAO : Mem.range_perm mf pa 0 128 Cur Freeable) by (keep_free FA2 FrameS).
 assert (FBO : Mem.range_perm mf pb 0 128 Cur Freeable) by (keep_free FB2 FrameS).
 assert (FTO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_free FT2 FrameS).
 assert (FlagO : Mem.load Mint32 mf pa 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameS Mint32 pa 120);[exact Flag2| |intros pos Pos;split;congruence].
   eapply Mem.perm_valid_block;apply (FA2 0);lia. }
 assert (Frame : lframe (gej_add_nonzero_start_frame pa pb bh bt b2) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact Frame0|];intros bx pos (NA & NB & NH & NT & N2) VB;left;exact NA.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameT|];intros bx pos (NA & NB & NH & NT & N2) VB;
         split;[exact NT|];split;[exact NH|];left;exact NB.
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FrameZ|];intros bx pos (NA & NB & NH & NT & N2) VB;split;assumption.
       * eapply lframe_implies;[exact FrameS|];intros bx pos (NA & NB & NH & NT & N2) VB;split;assumption. }
 exists mf;split.
 - unfold gej_add_nonzero_start_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m0) (le1:=le).
   + unfold mixed_clear_flag;eapply exec_Sassign with (loc:=pa) (ofs:=Ptrofs.repr 120) (bf:=Full)
       (v2:=Vint Int.zero) (v:=Vint Int.zero).
     * apply eval_double_flag_field;exact PR.
     * constructor.
     * reflexivity.
     * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=le).
     * unfold gej_add_t_mul;eapply exec_curve_call with
         (vargs:=[Vptr bt Ptrofs.zero;Vptr bh Ptrofs.zero;Vptr pb (Ptrofs.repr 80)]) (v:=Vundef).
       -- original_pure.
       -- exact EM.
       -- eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|].
          eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|].
          eapply eval_Econs with (v1:=Vptr pb (Ptrofs.repr 80));
            [apply eval_double_point_address;[cbn [In];tauto|exact PB]|reflexivity|constructor].
       -- exact CT.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=le).
       -- unfold gej_add_null_ratio;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
          ++ apply eval_double_var_null_test;exact PN.
          ++ reflexivity.
          ++ apply exec_Sskip.
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le).
          ++ unfold gej_add_z_mul;eapply exec_curve_call with
               (vargs:=[Vptr pa (Ptrofs.repr 80);Vptr pa (Ptrofs.repr 80);Vptr bt Ptrofs.zero]) (v:=Vundef).
             ** original_pure.
             ** exact EM.
             ** eapply eval_Econs with (v1:=Vptr pa (Ptrofs.repr 80));
                  [apply eval_double_point_address;[cbn [In];tauto|exact PR]|reflexivity|].
                eapply eval_Econs with (v1:=Vptr pa (Ptrofs.repr 80));
                  [apply eval_double_point_address;[cbn [In];tauto|exact PA]|reflexivity|].
                eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|constructor].
             ** exact CZ.
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
             ** unfold mixed_h_square;eapply exec_curve_call with (vargs:=[Vptr b2 Ptrofs.zero;Vptr bh Ptrofs.zero]) (v:=Vundef).
                --- original_pure.
                --- exact EQ.
                --- eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
                    eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|constructor].
                --- exact CS.
             ** apply exec_Sskip.
 - repeat (first [assumption|split]).
Qed.

Definition gej_add_nonzero_prefix_statements := mixed_zero_head :: gej_add_nonzero_start_statements.
Lemma gej_add_nonzero_prefix_source : gej_add_after 14=
 statement_sequence gej_add_nonzero_prefix_statements (gej_add_after 20).
Proof. reflexivity. Qed.

Theorem exec_gej_add_nonzero_prefix e le m pa pb bh bt b2 x y z w h :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 le!_r=Some (Vptr pa Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 e!_h=Some (bh,curve_fe_type) -> e!_t=Some (bt,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> NoDup [pa;pb;bh;bt;b2] ->
 square_input_bounds z -> square_input_bounds w -> square_input_bounds h -> radix_value h mod feP<>0 ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 80 (words5 w) -> fe_at m bh 0 (words5 h) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence gej_add_nonzero_prefix_statements Sskip) E0
   (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
 fe_at mf pa 0 (words5 x) /\ fe_at mf pa 40 (words5 y) /\
 fe_at mf pa 80 (words5 (point_mul_words z (point_mul_words h w))) /\
 Mem.load Mint32 mf pa 120=Some (Vint Int.zero) /\
 fe_at mf pb 80 (words5 w) /\ fe_at mf bh 0 (words5 h) /\
 fe_at mf bt 0 (words5 (point_mul_words h w)) /\ fe_at mf b2 0 (words5 (square_words h)) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
 square_input_bounds (point_mul_words z (point_mul_words h w)) /\
 square_input_bounds (square_words h) /\
 lframe (gej_add_nonzero_start_frame pa pb bh bt b2) m mf.
Proof.
 intros PA PB PR PN EH ET E2 EN EM EQ Sep BZ BW BH HNZ X Y Z W H FA FB FH FT F2.
 pose proof Sep as Sep0;separate_blocks Sep.
 destruct (exec_mixed_nonzero_guard h e le m bh EH EN BH HNZ H FH)
   as (mg & Guard & HG & FHG & FrameG).
 assert (XG : fe_at mg pa 0 (words5 x)) by (keep_field X FrameG).
 assert (YG : fe_at mg pa 40 (words5 y)) by (keep_field Y FrameG).
 assert (ZG : fe_at mg pa 80 (words5 z)) by (keep_field Z FrameG).
 assert (WG : fe_at mg pb 80 (words5 w)) by (keep_field W FrameG).
 assert (FAG : Mem.range_perm mg pa 0 128 Cur Freeable) by (keep_free FA FrameG).
 assert (FBG : Mem.range_perm mg pb 0 128 Cur Freeable) by (keep_free FB FrameG).
 assert (FTG : Mem.range_perm mg bt 0 40 Cur Freeable) by (keep_free FT FrameG).
 assert (F2G : Mem.range_perm mg b2 0 40 Cur Freeable) by (keep_free F2 FrameG).
 set (lg := PTree.set _t'2 (Vint Int.zero) le).
 assert (PAG : lg!_a=Some (Vptr pa Ptrofs.zero)) by
   (unfold lg;rewrite PTree.gso by discriminate;exact PA).
 assert (PBG : lg!_b=Some (Vptr pb Ptrofs.zero)) by
   (unfold lg;rewrite PTree.gso by discriminate;exact PB).
 assert (PRG : lg!_r=Some (Vptr pa Ptrofs.zero)) by
   (unfold lg;rewrite PTree.gso by discriminate;exact PR).
 assert (PNG : lg!_rzr=Some (Vlong Int64.zero)) by
   (unfold lg;rewrite PTree.gso by discriminate;exact PN).
 destruct (exec_gej_add_nonzero_start e lg mg pa pb bh bt b2 x y z w h
   PAG PBG PRG PNG EH ET E2 EM EQ Sep0 BZ BW BH XG YG ZG WG HG FAG FBG FHG FTG F2G)
   as (mf & Start & XO & YO & ZO & FlagO & WO & HO & TO & H2O &
     FAO & FBO & FHO & FTO & F2O & BoundZ & BoundH & FrameS).
 assert (Frame : lframe (gej_add_nonzero_start_frame pa pb bh bt b2) m mf).
 { eapply lframe_trans;[|exact FrameS].
   eapply lframe_implies;[exact FrameG|].
   intros bx pos (NA & NB & NH & NT & N2) VB;exact NH. }
 exists mf;split.
 - unfold gej_add_nonzero_prefix_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mg) (le1:=lg);[exact Guard|exact Start].
 - repeat (first [assumption|split]).
Qed.

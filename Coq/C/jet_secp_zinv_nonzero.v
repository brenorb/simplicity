(** Original zinv nonzero-H start; no ratio-pointer statement occurs here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_mixed_zero C.jet_secp_double_statements
  C.jet_secp_double_flag C.jet_secp_double_var_owned C.jet_secp_double_var_statements
  C.jet_secp_point_mul_numeric C.jet_secp_point_mul_preservation C.jet_secp_point_write_run
  C.jet_secp_square_separate_caller C.jet_secp_statement_prefix C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_mixed_difference C.jet_secp_mixed_nonzero_start C.jet_secp_zinv_zero
  C.jet_secp_zinv_differences C.jet_secp_mixed_after_square C.jet_secp_mixed_nonzero_tail.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.

Definition zinv_nonzero_start_statements := [mixed_clear_flag;mixed_z_mul;mixed_h_square].
Lemma zinv_nonzero_start_source : zinv_after_zero=
  statement_sequence zinv_nonzero_start_statements mixed_after_h_square.
Proof. reflexivity. Qed.

Local Ltac keep_start_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_start_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_zinv_nonzero_start e le m bp bh b2 x y z h :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
  e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> bp<>bh -> bp<>b2 -> bh<>b2 ->
  square_input_bounds z -> square_input_bounds h ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bh 0 (words5 h) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_nonzero_start_statements Sskip) E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf b2 0 (words5 (square_words h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (square_words h) /\
  radix_value (point_mul_words z h) mod field_prime=(radix_value z*radix_value h) mod field_prime /\
  radix_value (square_words h) mod field_prime=(radix_value h*radix_value h) mod field_prime /\
  lframe (mixed_nonzero_start_frame bp bh b2) m mf.
Proof.
  intros HA HR EH E2 EM EQ SPH SP2 SH2 BZ BH X Y Z H PF HF F2.
  destruct (double_var_store_flag x y z m bp Int.zero X Y Z PF)
    as (m0 & Store & Flag0 & X0 & Y0 & Z0 & PF0 & Frame0).
  assert (H0 : fe_at m0 bh 0 (words5 h)).
  { eapply field_at_lframe;[exact H|exact Frame0|];intro pos;left;congruence. }
  assert (HF0 : Mem.range_perm m0 bh 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact HF|exact Frame0|];intro pos;left;congruence. }
  assert (F20 : Mem.range_perm m0 b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2|exact Frame0|];intro pos;left;congruence. }
  destruct (eval_point_mul_numeric PointZ z h m0 bp bh BZ BH SPH Z0 PF0 H0 HF0)
    as (mz & CM & Z1 & PF1 & H1 & HF1 & ValZ & BoundZ & RawFrame1).
  pose proof (point_mul_external_frame PointZ m0 mz bp bh RawFrame1) as Frame1.
  assert (X1 : fe_at mz bp 0 (words5 x)).
  { exact (point_mul_other_field PointZ PointX m0 mz bp bh x ltac:(discriminate) SPH X0 PF1 RawFrame1). }
  assert (Y1 : fe_at mz bp 40 (words5 y)).
  { exact (point_mul_other_field PointZ PointY m0 mz bp bh y ltac:(discriminate) SPH Y0 PF1 RawFrame1). }
  assert (F21 : Mem.range_perm mz b2 0 40 Cur Freeable) by (keep_start_free F20 Frame1).
  assert (Flag1 : Mem.load Mint32 mz bp 120=Some (Vint Int.zero)).
  { eapply point_mul_flag;[exact SPH| |exact Flag0|exact RawFrame1].
    eapply Mem.perm_valid_block;apply (PF0 0);lia. }
  destruct (eval_square_separate_from_storage h mz b2 bh BH F21 H1 HF1 ltac:(congruence))
    as (mf & CS & H2O & F2O & HO & HFO & ValH & BoundH & Frame2).
  assert (XO : fe_at mf bp 0 (words5 x)) by (keep_start_field X1 Frame2).
  assert (YO : fe_at mf bp 40 (words5 y)) by (keep_start_field Y1 Frame2).
  assert (ZO : fe_at mf bp 80 (words5 (point_mul_words z h))) by (keep_start_field Z1 Frame2).
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable) by (keep_start_free PF1 Frame2).
  assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 Frame2 Mint32 bp 120);[exact Flag1| |intros pos HP;split;congruence].
    eapply Mem.perm_valid_block;apply (PF1 0);lia. }
  assert (Frame : lframe (mixed_nonzero_start_frame bp bh b2) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact Frame0|];intros bx pos (NH & N2 & NP) HV.
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;lia|right;right;exact NP].
    - eapply lframe_trans.
      + eapply lframe_implies;[exact RawFrame1|];intros bx pos (NH & N2 & NP) HV HFt.
        destruct (point_mul_foot_bounds PointZ bp bh bx pos HFt) as [[HE HP]|HE];[|contradiction].
        subst bx;change (80<=pos<120) in HP;destruct NP as [NP|[NP|NP]];[contradiction|lia|lia].
      + eapply lframe_implies;[exact Frame2|];intros bx pos (NH & N2 & NP) HV;split;assumption. }
  exists mf;split.
  - unfold zinv_nonzero_start_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m0) (le1:=le).
    + unfold mixed_clear_flag;eapply exec_Sassign with (loc:=bp) (ofs:=Ptrofs.repr 120) (bf:=Full)
        (v2:=Vint Int.zero) (v:=Vint Int.zero).
      * apply eval_double_flag_field;exact HR.
      * constructor.
      * reflexivity.
      * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le).
      * unfold mixed_z_mul;eapply exec_curve_call with
             (vargs:=[Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 80);Vptr bh Ptrofs.zero]) (v:=Vundef).
        -- original_pure.
        -- exact EM.
        -- eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 80));
                [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
              eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 80));
                [apply eval_double_point_address;[cbn [In];tauto|exact HA]|reflexivity|].
              eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|constructor].
        -- exact CM.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
        -- unfold mixed_h_square;eapply exec_curve_call with (vargs:=[Vptr b2 Ptrofs.zero;Vptr bh Ptrofs.zero]) (v:=Vundef).
           ++ original_pure.
           ++ exact EQ.
           ++ eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
                 eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|constructor].
           ++ exact CS.
        -- apply exec_Sskip.
  - repeat (first [assumption|split]).
Qed.

Lemma zinv_nonzero_source : zinv_after_difference =
 Ssequence zinv_zero_head (statement_sequence zinv_nonzero_start_statements mixed_after_h_square).
Proof. reflexivity. Qed.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.
Local Ltac outside_start := unfold mixed_nonzero_start_frame;
 repeat split;try (left;congruence);congruence.

Theorem exec_zinv_nonzero_tail e le m bp bh b2 b3 bt bu bi bs x y z h u i s :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
 e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> NoDup [bp;bh;b2;b3;bt;bu;bi;bs] ->
 square_input_bounds z -> square_input_bounds h -> square_input_bounds u -> square_input_bounds i -> square_input_bounds s ->
 radix_value h mod feP<>0 -> fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) -> fe_at m bi 0 (words5 i) -> fe_at m bs 0 (words5 s) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
 Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_after_difference E0 (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
 fe_at mf bp 0 (words5 (mixed_nonzero_x_words h i u)) /\
 fe_at mf bp 40 (words5 (mixed_nonzero_y_words h i u s)) /\
 fe_at mf bp 80 (words5 (point_mul_words z h)) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
 Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
 square_input_bounds (mixed_nonzero_x_words h i u) /\ square_input_bounds (mixed_nonzero_y_words h i u s) /\
 square_input_bounds (point_mul_words z h) /\ lframe (mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs) m mf.
Proof.
 intros HA HR EH E2 E3 ET EU EI ES EZ EM EQ EN EA Sep BZ BH BU BI BS HNZ X Y ZAt H U I S PF FH F2 F3 FT FU IF SF.
 pose proof Sep as SepAll;separate_blocks Sep.
 destruct (exec_zinv_nonzero_guard h e le m bh EH EZ BH HNZ H FH)
   as (mg & Guard & HG & FHG & FG).
 assert (XG : fe_at mg bp 0 (words5 x)) by (keep_start_field X FG).
 assert (YG : fe_at mg bp 40 (words5 y)) by (keep_start_field Y FG).
 assert (ZG : fe_at mg bp 80 (words5 z)) by (keep_start_field ZAt FG).
 assert (UG : fe_at mg bu 0 (words5 u)) by (keep_start_field U FG).
 assert (IG : fe_at mg bi 0 (words5 i)) by (keep_start_field I FG).
 assert (SG : fe_at mg bs 0 (words5 s)) by (keep_start_field S FG).
 assert (PFG : Mem.range_perm mg bp 0 128 Cur Freeable) by (keep_start_free PF FG).
 assert (F2G : Mem.range_perm mg b2 0 40 Cur Freeable) by (keep_start_free F2 FG).
 assert (F3G : Mem.range_perm mg b3 0 40 Cur Freeable) by (keep_start_free F3 FG).
 assert (FTG : Mem.range_perm mg bt 0 40 Cur Freeable) by (keep_start_free FT FG).
 assert (FUG : Mem.range_perm mg bu 0 40 Cur Freeable) by (keep_start_free FU FG).
 assert (IFG : Mem.range_perm mg bi 0 40 Cur Freeable) by (keep_start_free IF FG).
 assert (SFG : Mem.range_perm mg bs 0 40 Cur Freeable) by (keep_start_free SF FG).
 set (lg := PTree.set _t'2 (Vint Int.zero) le).
 assert (HAG : lg!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lg;rewrite PTree.gso by discriminate;exact HA).
 assert (HRG : lg!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lg;rewrite PTree.gso by discriminate;exact HR).
 destruct (exec_zinv_nonzero_start e lg mg bp bh b2 x y z h HAG HRG EH E2 EM EQ
   ltac:(congruence) ltac:(congruence) ltac:(congruence) BZ BH XG YG ZG HG PFG FHG F2G)
   as (mp & Start & XP & YP & ZP & FlagP & HP & H2P & PFP & FHP & F2P & BoundZ & BoundH2 & ValZ & ValH & FP).
 assert (UP : fe_at mp bu 0 (words5 u)).
 { eapply field_at_lframe;[exact UG|exact FP|];intro pos;outside_start. }
 assert (IP : fe_at mp bi 0 (words5 i)).
 { eapply field_at_lframe;[exact IG|exact FP|];intro pos;outside_start. }
 assert (SP : fe_at mp bs 0 (words5 s)).
 { eapply field_at_lframe;[exact SG|exact FP|];intro pos;outside_start. }
 assert (F3P : Mem.range_perm mp b3 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F3G|exact FP|];intro pos;outside_start. }
 assert (FTP : Mem.range_perm mp bt 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FTG|exact FP|];intro pos;outside_start. }
 assert (FUP : Mem.range_perm mp bu 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FUG|exact FP|];intro pos;outside_start. }
 assert (IFP : Mem.range_perm mp bi 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact IFG|exact FP|];intro pos;outside_start. }
 assert (SFP : Mem.range_perm mp bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact SFG|exact FP|];intro pos;outside_start. }
 destruct (exec_mixed_after_h_square e lg mp bp bh b2 b3 bt bu bi bs (point_mul_words z h) h u i s
   HRG EH E2 E3 ET EU EI ES EM EQ EN EA SepAll BH BU BI BS ZP FlagP HP H2P UP IP SP PFP FHP F2P F3P FTP FUP IFP SFP)
   as (mf & Rest & XO & YO & ZO & FlagO & PFO & FHO & F2O & F3O & FTO & FUO & IFO & SFO & BX & BY & FR).
 assert (Frame : lframe (mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FG|];intros bx pos (NH & N2 & N3 & NT & NU & NI & NS & NP) Valid;exact NH.
   - eapply lframe_trans;[|exact FR].
     eapply lframe_implies;[exact FP|];intros bx pos (NH & N2 & N3 & NT & NU & NI & NS & NP) Valid.
     unfold mixed_nonzero_start_frame;split;[exact NH|];split;[exact N2|].
     destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;clear - NP;lia|right;right;exact NP]. }
 exists mf;split.
 - rewrite zinv_nonzero_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mg) (le1:=lg);[exact Guard|].
   eapply exec_statement_prefix_then_last;[exact Start|exact Rest].
 - repeat first [assumption|split].
Qed.

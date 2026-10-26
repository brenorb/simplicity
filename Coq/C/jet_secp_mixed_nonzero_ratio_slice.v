(** Original nonzero-H mixed-addition tail with a ratio array slice. The
    indexed H copy is followed by the existing checked product/XY calls;
    neighboring ratio entries and the full caller array owner are preserved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_mixed_zero C.jet_secp_double_statements
  C.jet_secp_double_flag C.jet_secp_double_var_owned C.jet_secp_double_var_statements
  C.jet_secp_point_mul_numeric C.jet_secp_point_mul_preservation C.jet_secp_point_write_run
  C.jet_secp_square_separate_caller C.jet_secp_statement_prefix C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_mixed_difference C.jet_secp_mixed_nonzero_start C.jet_secp_mixed_nonzero_products
  C.jet_secp_mixed_nonzero_tail C.jet_secp_field_copy_owned C.jet_secp_double_var_ratio
  C.jet_secp_mixed_products C.jet_secp_mixed_x_tail C.jet_secp_mixed_y_tail C.jet_secp_field_mul_small
  C.jet_secp_double_coordinate_numeric C.jet_secp_field_sum_bounds C.jet_secp_double_var_ratio_slice.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.

Definition mixed_nonzero_start_slice_frame (bp bh b2 br : block) base (bx:block) (pos:Z) :=
  mixed_nonzero_start_frame bp bh b2 bx pos /\ (bx<>br \/ pos<base \/ base+40<=pos).

Local Ltac keep_start_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_start_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac separate_ratio_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac sep_goal := repeat rewrite NoDup_cons_iff;cbn [In];repeat split;
  try apply NoDup_nil;try (let Hx := fresh "Hx" in intro Hx;repeat (destruct Hx as [Hx|Hx]);try contradiction;congruence).
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_mixed_nonzero_start_slice e le m bp bh b2 br base size x y z h :
  0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
  le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
  e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> bp<>bh -> bp<>b2 -> bh<>b2 ->
  bp<>br -> bh<>br -> b2<>br ->
  square_input_bounds z -> square_input_bounds h ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bh 0 (words5 h) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m br 0 size Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_nonzero_start_statements Sskip) E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf b2 0 (words5 (square_words h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (square_words h) /\
  radix_value (point_mul_words z h) mod field_prime=(radix_value z*radix_value h) mod field_prime /\
  radix_value (square_words h) mod field_prime=(radix_value h*radix_value h) mod field_prime /\
  fe_at mf br base (words5 h) /\ Mem.range_perm mf br 0 size Cur Freeable /\
  lframe (mixed_nonzero_start_slice_frame bp bh b2 br base) m mf.
Proof.
  intros Base Align Fit Max HA HR HN EH E2 EM EQ SPH SP2 SH2 SPR SHR S2R BZ BH X Y Z H PF HF F2 RF.
  destruct (double_var_store_flag x y z m bp Int.zero X Y Z PF)
    as (m0 & Store & Flag0 & X0 & Y0 & Z0 & PF0 & Frame0).
  assert (H0 : fe_at m0 bh 0 (words5 h)).
  { eapply field_at_lframe;[exact H|exact Frame0|];intro pos;left;congruence. }
  assert (HF0 : Mem.range_perm m0 bh 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact HF|exact Frame0|];intro pos;left;congruence. }
  assert (F20 : Mem.range_perm m0 b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2|exact Frame0|];intro pos;left;congruence. }
  assert (RF0 : Mem.range_perm m0 br 0 size Cur Freeable).
  { eapply curve_keep_free;[lia|exact RF|exact Frame0|];intro pos;left;congruence. }
  destruct (exec_field_copy_owned e le m0 (Evar _h curve_fe_type)
    (Ederef (Etempvar _rzr (tptr curve_fe_type)) curve_fe_type) bh 0 br base h eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_Evar_local;exact EH|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_Ederef;apply eval_Etempvar;exact HN)
    SHR H0 Base Align ltac:(lia) ltac:(intros pos Range;apply RF0;lia))
    as (mc & Copy & RC & PermC & FrameC).
  assert (XC : fe_at mc bp 0 (words5 x)) by (eapply field_at_lframe;[exact X0|exact FrameC|];intro pos;left;congruence).
  assert (YC : fe_at mc bp 40 (words5 y)) by (eapply field_at_lframe;[exact Y0|exact FrameC|];intro pos;left;congruence).
  assert (ZC : fe_at mc bp 80 (words5 z)) by (eapply field_at_lframe;[exact Z0|exact FrameC|];intro pos;left;congruence).
  assert (HC : fe_at mc bh 0 (words5 h)) by (eapply field_at_lframe;[exact H0|exact FrameC|];intro pos;left;congruence).
  assert (PFC : Mem.range_perm mc bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact PF0|exact FrameC|];intro pos;left;congruence. }
  assert (HFC : Mem.range_perm mc bh 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact HF0|exact FrameC|];intro pos;left;congruence. }
  assert (F2C : Mem.range_perm mc b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F20|exact FrameC|];intro pos;left;congruence. }
  assert (RFC : Mem.range_perm mc br 0 size Cur Freeable).
  { intros pos HP;apply (proj2 (PermC br pos Cur Freeable));apply RF0;exact HP. }
  assert (FlagC : Mem.load Mint32 mc bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FrameC Mint32 bp 120);[exact Flag0| |intros pos HP;left;congruence].
    eapply Mem.perm_valid_block;apply (PF0 0);lia. }
  destruct (eval_point_mul_numeric PointZ z h mc bp bh BZ BH SPH ZC PFC HC HFC)
    as (mz & CM & Z1 & PF1 & H1 & HF1 & ValZ & BoundZ & RawFrame1).
  pose proof (point_mul_external_frame PointZ mc mz bp bh RawFrame1) as Frame1.
  assert (X1 : fe_at mz bp 0 (words5 x)).
  { exact (point_mul_other_field PointZ PointX mc mz bp bh x ltac:(discriminate) SPH XC PF1 RawFrame1). }
  assert (Y1 : fe_at mz bp 40 (words5 y)).
  { exact (point_mul_other_field PointZ PointY mc mz bp bh y ltac:(discriminate) SPH YC PF1 RawFrame1). }
  assert (F21 : Mem.range_perm mz b2 0 40 Cur Freeable) by (keep_start_free F2C Frame1).
  assert (R1 : fe_at mz br base (words5 h)) by (keep_start_field RC Frame1).
  assert (RF1 : Mem.range_perm mz br 0 size Cur Freeable) by (keep_start_free RFC Frame1).
  assert (Flag1 : Mem.load Mint32 mz bp 120=Some (Vint Int.zero)).
  { eapply point_mul_flag;[exact SPH| |exact FlagC|exact RawFrame1].
    eapply Mem.perm_valid_block;apply (PFC 0);lia. }
  destruct (eval_square_separate_from_storage h mz b2 bh BH F21 H1 HF1 ltac:(congruence))
    as (mf & CS & H2O & F2O & HO & HFO & ValH & BoundH & Frame2).
  assert (XO : fe_at mf bp 0 (words5 x)) by (keep_start_field X1 Frame2).
  assert (YO : fe_at mf bp 40 (words5 y)) by (keep_start_field Y1 Frame2).
  assert (ZO : fe_at mf bp 80 (words5 (point_mul_words z h))) by (keep_start_field Z1 Frame2).
  assert (RO : fe_at mf br base (words5 h)) by (keep_start_field R1 Frame2).
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable) by (keep_start_free PF1 Frame2).
  assert (RFO : Mem.range_perm mf br 0 size Cur Freeable) by (keep_start_free RF1 Frame2).
  assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 Frame2 Mint32 bp 120);[exact Flag1| |intros pos HP;split;congruence].
    eapply Mem.perm_valid_block;apply (PF1 0);lia. }
  assert (Frame : lframe (mixed_nonzero_start_slice_frame bp bh b2 br base) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact Frame0|];intros bx pos ((NH & N2 & NP) & NR) HV.
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;lia|right;right;exact NP].
    - eapply lframe_trans.
      + eapply lframe_implies;[exact FrameC|];intros bx pos ((NH & N2 & NP) & NR) HV;exact NR.
      + eapply lframe_trans.
        * eapply lframe_implies;[exact RawFrame1|];intros bx pos ((NH & N2 & NP) & NR) HV HFt.
          destruct (point_mul_foot_bounds PointZ bp bh bx pos HFt) as [[HE HP]|HE];[|contradiction].
          subst bx;change (80<=pos<120) in HP;destruct NP as [NP|[NP|NP]];[contradiction|lia|lia].
        * eapply lframe_implies;[exact Frame2|];intros bx pos ((NH & N2 & NP) & NR) HV;split;assumption. }
  exists mf;split.
  - unfold mixed_nonzero_start_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m0) (le1:=le).
    + unfold mixed_clear_flag;eapply exec_Sassign with (loc:=bp) (ofs:=Ptrofs.repr 120) (bf:=Full)
        (v2:=Vint Int.zero) (v:=Vint Int.zero).
      * apply eval_double_flag_field;exact HR.
      * constructor.
      * reflexivity.
      * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le).
      * unfold mixed_null_ratio;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
        -- apply eval_double_var_nonnull_slice with (br:=br) (base:=base);[lia|exact HN|].
           apply Mem.valid_pointer_nonempty_perm;
             eapply Mem.perm_implies;[apply (RF0 base);lia|constructor].
        -- reflexivity.
        -- exact Copy.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le).
        -- unfold mixed_z_mul;eapply exec_curve_call with
             (vargs:=[Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 80);Vptr bh Ptrofs.zero]) (v:=Vundef).
           ++ original_pure.
           ++ exact EM.
           ++ eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 80));
                [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
              eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 80));
                [apply eval_double_point_address;[cbn [In];tauto|exact HA]|reflexivity|].
              eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|constructor].
           ++ exact CM.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
           ++ unfold mixed_h_square;eapply exec_curve_call with (vargs:=[Vptr b2 Ptrofs.zero;Vptr bh Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact EQ.
              ** eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
                 eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|constructor].
              ** exact CS.
           ++ apply exec_Sskip.
  - repeat (first [assumption|split]).
Qed.

Theorem exec_mixed_nonzero_prefix_slice e le m bp bh b2 br base size x y z h :
  0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
  le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  bp<>bh -> bp<>b2 -> bh<>b2 -> bp<>br -> bh<>br -> b2<>br ->
  square_input_bounds z -> square_input_bounds h -> radix_value h mod feP<>0 ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bh 0 (words5 h) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m br 0 size Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_nonzero_prefix_statements Sskip) E0
    (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\ fe_at mf bh 0 (words5 h) /\ fe_at mf b2 0 (words5 (square_words h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (square_words h) /\
  radix_value (point_mul_words z h) mod field_prime=(radix_value z*radix_value h) mod field_prime /\
  radix_value (square_words h) mod field_prime=(radix_value h*radix_value h) mod field_prime /\
  fe_at mf br base (words5 h) /\ Mem.range_perm mf br 0 size Cur Freeable /\
  lframe (mixed_nonzero_start_slice_frame bp bh b2 br base) m mf.
Proof.
  intros Base Align Fit Max HA HR HN EH E2 EN EM EQ SPH SP2 SH2 SPR SHR S2R BZ BH HNZ X Y Z H PF HF F2 RF.
  destruct (exec_mixed_nonzero_guard h e le m bh EH EN BH HNZ H HF)
    as (mg & CG & HG & HFG & FG).
  assert (XG : fe_at mg bp 0 (words5 x)) by (keep_start_field X FG).
  assert (YG : fe_at mg bp 40 (words5 y)) by (keep_start_field Y FG).
  assert (ZG : fe_at mg bp 80 (words5 z)) by (keep_start_field Z FG).
  assert (PFG : Mem.range_perm mg bp 0 128 Cur Freeable) by (keep_start_free PF FG).
  assert (F2G : Mem.range_perm mg b2 0 40 Cur Freeable) by (keep_start_free F2 FG).
  assert (RFG : Mem.range_perm mg br 0 size Cur Freeable) by (keep_start_free RF FG).
  assert (HAG : (PTree.set _t'2 (Vint Int.zero) le)!_a=Some (Vptr bp Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HA).
  assert (HRG : (PTree.set _t'2 (Vint Int.zero) le)!_r=Some (Vptr bp Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HR).
  assert (HNG : (PTree.set _t'2 (Vint Int.zero) le)!_rzr=Some (Vptr br (Ptrofs.repr base)))
    by (rewrite PTree.gso by discriminate;exact HN).
  destruct (exec_mixed_nonzero_start_slice e (PTree.set _t'2 (Vint Int.zero) le) mg bp bh b2 br base size x y z h
    Base Align Fit Max HAG HRG HNG EH E2 EM EQ SPH SP2 SH2 SPR SHR S2R BZ BH XG YG ZG HG PFG HFG F2G RFG)
    as (mf & CS & XO & YO & ZO & FlagO & HO & H2O & PFO & HFO & F2O & BoundZ & BoundH & ValZ & ValH & RO & RFO & FS).
  assert (Frame : lframe (mixed_nonzero_start_slice_frame bp bh b2 br base) m mf).
  { eapply lframe_trans;[|exact FS].
    eapply lframe_implies;[exact FG|];intros bx pos ((NH & N2 & NP) & NR) HV;exact NH. }
  exists mf;split.
  - unfold mixed_nonzero_prefix_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mg) (le1:=PTree.set _t'2 (Vint Int.zero) le);
      [exact CG|exact CS].
  - repeat (first [assumption|split]).
Qed.

Definition mixed_nonzero_products_slice_frame (bp bh b2 b3 bt bu br : block) base (bx:block) (pos:Z) :=
  mixed_nonzero_products_frame bp bh b2 b3 bt bu bx pos /\ (bx<>br \/ pos<base \/ base+40<=pos).

Theorem exec_mixed_nonzero_products_slice e le m bp bh b2 b3 bt bu br base size x y z h u :
  0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
  e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_negate=None ->
  NoDup [bp;bh;b2;b3;bt;bu;br] -> square_input_bounds z -> square_input_bounds h -> square_input_bounds u ->
  radix_value h mod feP<>0 -> fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
  Mem.range_perm m br 0 size Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_nonzero_products_statements Sskip) E0
    (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf bu 0 (words5 u) /\ fe_at mf b2 0 (words5 (mixed_h2_words h)) /\
  fe_at mf b3 0 (words5 (mixed_h3_words h)) /\ fe_at mf bt 0 (words5 (mixed_t_words u h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (mixed_h2_words h) /\
  mul_small_input_bounds (mixed_h3_words h) /\ mul_small_input_bounds (mixed_t_words u h) /\
  radix_value (mixed_h2_words h)=4*feP-radix_value (square_words h) /\
  radix_value (mixed_h3_words h) mod feP=(radix_value (mixed_h2_words h)*radix_value h) mod feP /\
  radix_value (mixed_t_words u h) mod feP=(radix_value u*radix_value (mixed_h2_words h)) mod feP /\
  fe_at mf br base (words5 h) /\ Mem.range_perm mf br 0 size Cur Freeable /\
  lframe (mixed_nonzero_products_slice_frame bp bh b2 b3 bt bu br base) m mf.
Proof.
  intros Base Align Fit Max HA HR HN EH E2 E3 ET EU EZ EM EQ EN Sep BZ BH BU HNZ X Y Z H U PF FH F2 F3 FT FU RF.
  pose proof Sep as Sep0;separate_ratio_blocks Sep0.
  assert (SepP : NoDup [b2;b3;bt;bh;bu]).
  { sep_goal. }
  destruct (exec_mixed_nonzero_prefix_slice e le m bp bh b2 br base size x y z h Base Align Fit Max HA HR HN EH E2 EZ EM EQ
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    BZ BH HNZ X Y Z H PF FH F2 RF)
    as (mp & CP & XP & YP & ZP & FlagP & HP & H2P & PFP & FHP & F2P & BoundZ & BoundH2 & ValZ & ValH2 & RP & RFP & FP).
  assert (UP : fe_at mp bu 0 (words5 u)).
  { eapply field_at_lframe;[exact U|exact FP|];intro pos;unfold mixed_nonzero_start_slice_frame,mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  assert (F3P : Mem.range_perm mp b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3|exact FP|];intro pos;unfold mixed_nonzero_start_slice_frame,mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  assert (FTP : Mem.range_perm mp bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FT|exact FP|];intro pos;unfold mixed_nonzero_start_slice_frame,mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  assert (FUP : Mem.range_perm mp bu 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FU|exact FP|];intro pos;unfold mixed_nonzero_start_slice_frame,mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  destruct (exec_mixed_products e (PTree.set _t'2 (Vint Int.zero) le) mp b2 b3 bt bh bu (square_words h) h u
    E2 E3 ET EH EU EN EM SepP (double_square_tight h BH) BH BU H2P HP UP F2P F3P FTP FHP FUP)
    as (mf & CM & H2O & H3O & TO & HO & UO & F2O & F3O & FTO & FHO & FUO & ValN & BoundN & Val3 & ValT & Bound3 & BoundT & FM).
  assert (XO : fe_at mf bp 0 (words5 x)).
  { eapply field_at_lframe;[exact XP|exact FM|];intro pos;repeat split;congruence. }
  assert (YO : fe_at mf bp 40 (words5 y)).
  { eapply field_at_lframe;[exact YP|exact FM|];intro pos;repeat split;congruence. }
  assert (ZO : fe_at mf bp 80 (words5 (point_mul_words z h))).
  { eapply field_at_lframe;[exact ZP|exact FM|];intro pos;repeat split;congruence. }
  assert (RO : fe_at mf br base (words5 h)).
  { eapply field_at_lframe;[exact RP|exact FM|];intro pos;repeat split;congruence. }
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact PFP|exact FM|];intro pos;repeat split;congruence. }
  assert (RFO : Mem.range_perm mf br 0 size Cur Freeable).
  { eapply curve_keep_free;[clear -Base Fit;lia|exact RFP|exact FM|];intro pos;repeat split;congruence. }
  assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FM Mint32 bp 120);[exact FlagP| |intros pos PP;repeat split;congruence].
    eapply Mem.perm_valid_block;apply (PFP 0);lia. }
  assert (Frame : lframe (mixed_nonzero_products_slice_frame bp bh b2 b3 bt bu br base) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FP|];intros bx pos HQ HV;destruct HQ as (A & NR);destruct A as (N3 & NT & NU & NF).
      exact (conj NF NR).
    - eapply lframe_implies;[exact FM|];intros bx pos ((N3 & NT & NU & NH & N2 & NP) & NR) HV.
      unfold mixed_product_frame;repeat split;assumption. }
  exists mf;split.
  - change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence mixed_nonzero_prefix_statements (statement_sequence mixed_product_statements Sskip)) E0
      (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact CP|exact CM].
  - repeat (first [assumption|split]).
Qed.

Definition mixed_nonzero_tail_slice_frame (bp bh b2 b3 bt bu bi bs br : block) base (bx:block) (pos:Z) :=
  mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs bx pos /\ (bx<>br \/ pos<base \/ base+40<=pos).

Local Ltac keep_tail_free HF Frame :=
  eapply curve_keep_free;
   [first [match goal with HB0 : 0 <= ?start, Fit0 : ?start + 40 <= ?sz |- 0 < ?sz => clear -HB0 Fit0;lia end|lia]|
    exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac outside_products :=
  unfold mixed_nonzero_products_slice_frame,mixed_nonzero_products_frame,mixed_nonzero_start_frame;
    repeat split;try (left;congruence);congruence.

Theorem exec_mixed_nonzero_tail_slice e le m bp bh b2 b3 bt bu bi bs br base size x y z h u i s :
  0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
  e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> NoDup [bp;bh;b2;b3;bt;bu;bi;bs;br] ->
  square_input_bounds z -> square_input_bounds h -> square_input_bounds u -> square_input_bounds i -> square_input_bounds s ->
  radix_value h mod feP<>0 -> fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) -> fe_at m bi 0 (words5 i) -> fe_at m bs 0 (words5 s) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m br 0 size Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_after_difference E0 (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bp 0 (words5 (mixed_nonzero_x_words h i u)) /\
  fe_at mf bp 40 (words5 (mixed_nonzero_y_words h i u s)) /\
  fe_at mf bp 80 (words5 (point_mul_words z h)) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  square_input_bounds (mixed_nonzero_x_words h i u) /\ square_input_bounds (mixed_nonzero_y_words h i u s) /\
  square_input_bounds (point_mul_words z h) /\
  fe_at mf br base (words5 h) /\ Mem.range_perm mf br 0 size Cur Freeable /\
  lframe (mixed_nonzero_tail_slice_frame bp bh b2 b3 bt bu bi bs br base) m mf.
Proof.
  intros Base Align Fit Max HA HR HN EH E2 E3 ET EU EI ES EZ EM EQ EN EA Sep BZ BH BU BI BS HNZ X Y Z H U I S PF FH F2 F3 FT FU IF SF RF.
  pose proof Sep as Sep0;separate_ratio_blocks Sep0.
  assert (SepP : NoDup [bp;bh;b2;b3;bt;bu;br]) by sep_goal.
  assert (SepXY : NoDup [bp;bt;bi;b3;bs]) by sep_goal.
  destruct (exec_mixed_nonzero_products_slice e le m bp bh b2 b3 bt bu br base size x y z h u
    Base Align Fit Max HA HR HN EH E2 E3 ET EU EZ EM EQ EN SepP BZ BH BU HNZ X Y Z H U PF FH F2 F3 FT FU RF)
    as (mp & CP & XP & YP & ZP & FlagP & HP & UP & H2P & H3P & TP & PFP & FHP & F2P & F3P & FTP & FUP &
      BoundZ & BoundH2 & BoundH3 & BoundT & ValH2 & ValH3 & ValT & RP & RFP & FP).
  assert (IP : fe_at mp bi 0 (words5 i)).
  { eapply field_at_lframe;[exact I|exact FP|];intro pos;outside_products. }
  assert (SP : fe_at mp bs 0 (words5 s)).
  { eapply field_at_lframe;[exact S|exact FP|];intro pos;outside_products. }
  assert (IFP : Mem.range_perm mp bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact IF|exact FP|];intro pos;outside_products. }
  assert (SFP : Mem.range_perm mp bs 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact SF|exact FP|];intro pos;outside_products. }
  assert (HRP : (PTree.set _t'2 (Vint Int.zero) le)!_r=Some (Vptr bp Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HR).
  destruct (exec_mixed_xy_tail e (PTree.set _t'2 (Vint Int.zero) le) mp bp bi b3 bt bs
    i (mixed_h3_words h) (mixed_t_words u h) s HRP EI E3 ET ES EQ EM EA SepXY
    BI BoundH3 BoundT BS IP H3P TP SP PFP IFP F3P FTP SFP)
    as (mf & CXY & XO & YO & TO & GO & IO & SO & PFO & IFO & F3O & FTO & SFO & BoundX & BoundY & BoundTX & FX).
  assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_tail_free FHP FX).
  assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_tail_free F2P FX).
  assert (FUO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_tail_free FUP FX).
  assert (RFO : Mem.range_perm mf br 0 size Cur Freeable) by (keep_tail_free RFP FX).
  assert (RO : fe_at mf br base (words5 h)).
  { eapply field_at_lframe;[exact RP|exact FX|];intro pos;unfold mixed_xy_frame;repeat split;try (left;congruence);congruence. }
  assert (ZO : fe_at mf bp 80 (words5 (point_mul_words z h))).
  { eapply curve_keep_field_range;[reflexivity|exact ZP|exact FX|].
    intros pos HPos;unfold mixed_xy_frame;repeat split;try congruence;right;right;lia. }
  assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FX Mint32 bp 120);[exact FlagP| |].
    - eapply Mem.perm_valid_block;apply (PFP 0);lia.
    - intros pos HPos;unfold mixed_xy_frame;repeat split;try congruence;right;right;
        change (120<=pos<124) in HPos;lia. }
  assert (BX : square_input_bounds (mixed_nonzero_x_words h i u))
    by (exact (field_scaled_loose 4 _ ltac:(lia) BoundX)).
  assert (BY : square_input_bounds (mixed_nonzero_y_words h i u s))
    by (exact (field_scaled_loose 2 _ ltac:(lia) BoundY)).
  assert (Frame : lframe (mixed_nonzero_tail_slice_frame bp bh b2 b3 bt bu bi bs br base) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FP|];intros bx pos HQ HV;destruct HQ as ((NH & N2 & N3 & NT & NU & NI & NS & NP) & NR).
      unfold mixed_nonzero_products_slice_frame,mixed_nonzero_products_frame,mixed_nonzero_start_frame;
        split;[split;[exact N3|];split;[exact NT|];split;[exact NU|];split;[exact NH|];split;[exact N2|];
        destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;lia|right;right;exact NP]|exact NR].
    - eapply lframe_implies;[exact FX|];intros bx pos HQ HV;destruct HQ as ((NH & N2 & N3 & NT & NU & NI & NS & NP) & NR).
      unfold mixed_xy_frame;split;[exact NI|];split;[exact N3|];split;[exact NT|];split;[exact NS|].
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;exact NP|right;right;lia]. }
  exists mf;split.
  - rewrite mixed_nonzero_products_source;eapply exec_statement_prefix_then_last;[exact CP|exact CXY].
  - repeat (first [assumption|split]).
Qed.

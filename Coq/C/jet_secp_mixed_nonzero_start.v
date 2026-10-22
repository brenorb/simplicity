(** First four original nonzero-H statements: clear the flag, skip the NULL
    rzr write, multiply Z by H, and square H into an uninitialized temporary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_mixed_zero C.jet_secp_double_statements
  C.jet_secp_double_flag C.jet_secp_double_var_owned C.jet_secp_double_var_statements
  C.jet_secp_point_mul_numeric C.jet_secp_point_mul_preservation C.jet_secp_point_write_run
  C.jet_secp_square_separate_caller C.jet_secp_statement_prefix C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_mixed_difference.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.

Definition mixed_clear_flag := Sassign (double_point_field _r _infinity tint) (Econst_int Int.zero tint).
Definition mixed_null_ratio := Sifthenelse double_var_null_test
  (Sassign (Ederef (Etempvar _rzr (tptr curve_fe_type)) curve_fe_type) (Evar _h curve_fe_type)) Sskip.
Definition mixed_z_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [double_point_address _r _z;double_point_address _a _z;curve_local_address _h].
Definition mixed_h_square := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _h2;curve_local_address _h].
Definition mixed_nonzero_start_statements := [mixed_clear_flag;mixed_null_ratio;mixed_z_mul;mixed_h_square].
Definition mixed_after_h_square := match mixed_after_zero with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest))) => rest | _ => Sskip end.
Definition mixed_nonzero_start_frame (bp bh b2 bx : block) (pos : Z) :=
  bx<>bh /\ bx<>b2 /\ (bx<>bp \/ pos<80 \/ 124<=pos).
Lemma mixed_nonzero_start_source : mixed_after_zero=
  statement_sequence mixed_nonzero_start_statements mixed_after_h_square.
Proof. reflexivity. Qed.

Local Ltac keep_start_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_start_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_mixed_nonzero_start e le m bp bh b2 x y z h :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
  e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> bp<>bh -> bp<>b2 -> bh<>b2 ->
  square_input_bounds z -> square_input_bounds h ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bh 0 (words5 h) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_nonzero_start_statements Sskip) E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf b2 0 (words5 (square_words h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (square_words h) /\
  radix_value (point_mul_words z h) mod field_prime=(radix_value z*radix_value h) mod field_prime /\
  radix_value (square_words h) mod field_prime=(radix_value h*radix_value h) mod field_prime /\
  lframe (mixed_nonzero_start_frame bp bh b2) m mf.
Proof.
  intros HA HR HN EH E2 EM EQ SPH SP2 SH2 BZ BH X Y Z H PF HF F2.
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
  - unfold mixed_nonzero_start_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m0) (le1:=le).
    + unfold mixed_clear_flag;eapply exec_Sassign with (loc:=bp) (ofs:=Ptrofs.repr 120) (bf:=Full)
        (v2:=Vint Int.zero) (v:=Vint Int.zero).
      * apply eval_double_flag_field;exact HR.
      * constructor.
      * reflexivity.
      * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m0) (le1:=le).
      * unfold mixed_null_ratio;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
        -- apply eval_double_var_null_test;exact HN.
        -- reflexivity.
        -- apply exec_Sskip.
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

Definition mixed_nonzero_prefix_statements := mixed_zero_head::mixed_nonzero_start_statements.
Lemma mixed_nonzero_prefix_source : mixed_after_difference=
  statement_sequence mixed_nonzero_prefix_statements mixed_after_h_square.
Proof. reflexivity. Qed.

Theorem exec_mixed_nonzero_prefix e le m bp bh b2 x y z h :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  bp<>bh -> bp<>b2 -> bh<>b2 -> square_input_bounds z -> square_input_bounds h -> radix_value h mod feP<>0 ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bh 0 (words5 h) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_nonzero_prefix_statements Sskip) E0
    (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\ fe_at mf bh 0 (words5 h) /\ fe_at mf b2 0 (words5 (square_words h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (square_words h) /\
  radix_value (point_mul_words z h) mod field_prime=(radix_value z*radix_value h) mod field_prime /\
  radix_value (square_words h) mod field_prime=(radix_value h*radix_value h) mod field_prime /\
  lframe (mixed_nonzero_start_frame bp bh b2) m mf.
Proof.
  intros HA HR HN EH E2 EN EM EQ SPH SP2 SH2 BZ BH HNZ X Y Z H PF HF F2.
  destruct (exec_mixed_nonzero_guard h e le m bh EH EN BH HNZ H HF)
    as (mg & CG & HG & HFG & FG).
  assert (XG : fe_at mg bp 0 (words5 x)) by (keep_start_field X FG).
  assert (YG : fe_at mg bp 40 (words5 y)) by (keep_start_field Y FG).
  assert (ZG : fe_at mg bp 80 (words5 z)) by (keep_start_field Z FG).
  assert (PFG : Mem.range_perm mg bp 0 128 Cur Freeable) by (keep_start_free PF FG).
  assert (F2G : Mem.range_perm mg b2 0 40 Cur Freeable) by (keep_start_free F2 FG).
  assert (HAG : (PTree.set _t'2 (Vint Int.zero) le)!_a=Some (Vptr bp Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HA).
  assert (HRG : (PTree.set _t'2 (Vint Int.zero) le)!_r=Some (Vptr bp Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HR).
  assert (HNG : (PTree.set _t'2 (Vint Int.zero) le)!_rzr=Some (Vlong Int64.zero))
    by (rewrite PTree.gso by discriminate;exact HN).
  destruct (exec_mixed_nonzero_start e (PTree.set _t'2 (Vint Int.zero) le) mg bp bh b2 x y z h
    HAG HRG HNG EH E2 EM EQ SPH SP2 SH2 BZ BH XG YG ZG HG PFG HFG F2G)
    as (mf & CS & XO & YO & ZO & FlagO & HO & H2O & PFO & HFO & F2O & BoundZ & BoundH & ValZ & ValH & FS).
  assert (Frame : lframe (mixed_nonzero_start_frame bp bh b2) m mf).
  { eapply lframe_trans;[|exact FS].
    eapply lframe_implies;[exact FG|];intros bx pos (NH & N2 & NP) HV;exact NH. }
  exists mf;split.
  - unfold mixed_nonzero_prefix_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mg) (le1:=PTree.set _t'2 (Vint Int.zero) le);
      [exact CG|exact CS].
  - repeat (first [assumption|split]).
Qed.

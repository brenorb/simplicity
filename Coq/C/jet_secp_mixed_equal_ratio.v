(** Original mixed-addition equal-point dispatch with a non-NULL ratio.
    Both the I test and doubling execute from initial owned storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_field_zero_owned C.jet_secp_mixed_zero C.jet_secp_mixed_zero_branch
  C.jet_secp_double_var_owned C.jet_secp_double_all_calls C.jet_secp_double_var_ratio
  C.jet_secp_mixed_difference C.jet_secp_mixed_finite_return C.jet_secp_mixed_finite_prefix
  C.jet_secp_mixed_preparation C.jet_secp_statement_prefix C.jet_secp_double_coordinate_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Local Ltac keep_equal_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_equal_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_temp H := rewrite PTree.gso by discriminate;exact H.

Theorem exec_mixed_equal_ratio e le m bp bi br x y z i :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
  le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> bp<>bi -> bp<>br -> bi<>br ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds i ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  radix_value i mod feP=0 -> Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_zero_branch E0
    (PTree.set _t'1 (Vint Int.one) le) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (double_output_x_words x y)) /\
  fe_at mf bp 40 (words5 (double_output_y_words x y)) /\
  fe_at mf bp 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z)) /\
  fe_at mf bi 0 (words5 i) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  fe_at mf br 0 (words5 y) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>bi /\ bx<>br) m mf.
Proof.
  intros HA HR HN EI EN ED Sep SepR SepI BX BY BZ BI Tight IZ Flag X Y Z I PF IF RF.
  destruct (exec_mixed_zero_call true i e le m bi EI EN BI I IF)
    as (mz & CI & IZ0 & IF0 & FI).
  assert (VI : field_zero_result i=Int.one) by (unfold field_zero_result;rewrite IZ,Z.eqb_refl;reflexivity).
  rewrite VI in CI.
  assert (XZ : fe_at mz bp 0 (words5 x)) by (keep_equal_field X FI).
  assert (YZ : fe_at mz bp 40 (words5 y)) by (keep_equal_field Y FI).
  assert (ZZ : fe_at mz bp 80 (words5 z)) by (keep_equal_field Z FI).
  assert (PFZ : Mem.range_perm mz bp 0 128 Cur Freeable) by (keep_equal_free PF FI).
  assert (RFZ : Mem.range_perm mz br 0 40 Cur Freeable) by (keep_equal_free RF FI).
  assert (FlagZ : Mem.load Mint32 mz bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FI Mint32 bp 120);[exact Flag| |intros pos HP;exact Sep].
    eapply Mem.perm_valid_block;apply (PF 0);lia. }
  destruct (eval_double_var_finite_ratio x y z mz bp br SepR BX BY BZ Tight FlagZ XZ YZ ZZ PFZ RFZ)
    as (mf & CD & XO & YO & ZO & FlagO & PFO & BXO & BYO & BZO & RY & RFO & FD).
  assert (IO : fe_at mf bi 0 (words5 i)) by (keep_equal_field IZ0 FD).
  assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_equal_free IF0 FD).
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bi /\ bx<>br) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FI|];intros bx pos (NP & NI & NR) HV;exact NI.
    - eapply lframe_implies;[exact FD|];intros bx pos (NP & NI & NR) HV;split;assumption. }
  exists mf;split.
  - rewrite mixed_i_zero_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
      (le1:=PTree.set _t'1 (Vint Int.one) le).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz)
        (le1:=PTree.set _t'1 (Vint Int.one) le).
      * exact CI.
      * rewrite mixed_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
        -- apply eval_Etempvar;apply PTree.gss.
        -- reflexivity.
        -- unfold mixed_double_call;eapply exec_curve_call with
             (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr br Ptrofs.zero]) (v:=Vundef).
           ++ unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
           ++ exact ED.
           ++ eapply eval_Econs;[apply eval_Etempvar;keep_temp HR|reflexivity|].
              eapply eval_Econs;[apply eval_Etempvar;keep_temp HA|reflexivity|].
              eapply eval_Econs;[apply eval_Etempvar;keep_temp HN|reflexivity|constructor].
           ++ exact CD.
    + apply exec_Sreturn_none.
  - do 12 (split;[assumption|]);exact Frame.
Qed.

Local Ltac separate_equal_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.

(** The preceding H test also executes; its returning branch makes the
    remaining nonzero-H suffix unreachable on these initial values. *)
Theorem exec_mixed_equal_ratio_return e le m bp bh bi br x y z h i :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
  le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None ->
  bp<>bh -> bp<>bi -> bp<>br -> bh<>bi -> bh<>br -> bi<>br ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  square_input_bounds h -> square_input_bounds i ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  radix_value h mod feP=0 -> radix_value i mod feP=0 ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_after_difference E0
    (PTree.set _t'1 (Vint Int.one) (PTree.set _t'2 (Vint Int.one) le)) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (double_output_x_words x y)) /\
  fe_at mf bp 40 (words5 (double_output_y_words x y)) /\
  fe_at mf bp 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  fe_at mf br 0 (words5 y) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi /\ bx<>br) m mf.
Proof.
  intros HA HR HN EH EI EN ED SPH SPI SPR SHI SHR SIR BX BY BZ BH BI Tight H0 I0 Flag X Y Z H I PF HF IF RF.
  destruct (exec_mixed_zero_call false h e le m bh EH EN BH H HF)
    as (mh & CH & HH & HFH & FH).
  assert (VH : field_zero_result h=Int.one) by (unfold field_zero_result;rewrite H0,Z.eqb_refl;reflexivity).
  rewrite VH in CH.
  set (lh := PTree.set _t'2 (Vint Int.one) le).
  assert (HAH : lh!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lh;keep_temp HA).
  assert (HRH : lh!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lh;keep_temp HR).
  assert (HNH : lh!_rzr=Some (Vptr br Ptrofs.zero)) by (unfold lh;keep_temp HN).
  assert (XH : fe_at mh bp 0 (words5 x)) by (keep_equal_field X FH).
  assert (YH : fe_at mh bp 40 (words5 y)) by (keep_equal_field Y FH).
  assert (ZH : fe_at mh bp 80 (words5 z)) by (keep_equal_field Z FH).
  assert (IH : fe_at mh bi 0 (words5 i)) by (keep_equal_field I FH).
  assert (PFH : Mem.range_perm mh bp 0 128 Cur Freeable) by (keep_equal_free PF FH).
  assert (IFH : Mem.range_perm mh bi 0 40 Cur Freeable) by (keep_equal_free IF FH).
  assert (RFH : Mem.range_perm mh br 0 40 Cur Freeable) by (keep_equal_free RF FH).
  assert (FlagH : Mem.load Mint32 mh bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FH Mint32 bp 120);[exact Flag| |intros;exact SPH].
    eapply Mem.perm_valid_block;apply (PF 0);lia. }
  destruct (exec_mixed_equal_ratio e lh mh bp bi br x y z i
    HAH HRH HNH EI EN ED SPI SPR SIR BX BY BZ BI Tight I0 FlagH XH YH ZH IH PFH IFH RFH)
    as (mf & CB & XO & YO & ZO & FlagO & IO & PFO & IFO & BXO & BYO & BZO & RY & RFO & FB).
  assert (HFO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_equal_free HFH FB).
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi /\ bx<>br) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FH|];intros bx pos (NP & NH & NI & NR) HV;exact NH.
    - eapply lframe_implies;[exact FB|];intros bx pos (NP & NH & NI & NR) HV;repeat split;assumption. }
  exists mf;split.
  - rewrite mixed_zero_source;eapply exec_Sseq_2;[|discriminate].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mh) (le1:=lh);[exact CH|].
    eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
    + apply eval_Etempvar;unfold lh;apply PTree.gss.
    + reflexivity.
    + exact CB.
  - do 12 (split;[assumption|]);exact Frame.
Qed.

(** Complete original helper body on H=I=0, including all arithmetic before
    the tests.  Function entry and freeing the ten locals are separate. *)
Theorem exec_mixed_equal_ratio_body e le m bp ba bu bv bs bt bz bh bi br x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None ->
  NoDup [br;bh;bi;bp;ba;bu;bv;bs;bt;bz] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  radix_value (mixed_h_words x z u) mod feP=0 -> radix_value (mixed_i_words y z v) mod feP=0 ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (PTree.set _t'1 (Vint Int.one) (PTree.set _t'2 (Vint Int.one) (mixed_preparation_temps le)))
    mf (Out_return None) /\
  fe_at mf bp 0 (words5 (double_output_x_words x y)) /\
  fe_at mf bp 40 (words5 (double_output_y_words x y)) /\
  fe_at mf bp 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  fe_at mf br 0 (words5 y) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx pos=>mixed_finite_return_frame bp ba bu bv bs bt bz bh bi bx pos /\ bx<>br) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI EW EM EQ EN EA E0N ED Sep FlagA FlagB BX BY BZ BU BV H0 I0
    X Y Z U V PF AF UF VF SF TF ZF HF IF RF.
  assert (SepP : NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz]).
  { apply NoDup_cons_iff in Sep;exact (proj2 Sep). }
  pose proof Sep as Sep0;separate_equal_blocks Sep0.
  destruct (exec_mixed_finite_difference e le m bp ba bu bv bs bt bz bh bi x y z u v
    HA HB EU EV ES ET EZ EH EI EW EM EQ EN EA SepP FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF)
    as (mp & CP & XP & YP & ZP & UP & VP & U1 & U2 & S1 & S2 & Z12 & H & I & FlagAP & FlagBP &
      PFP & AFP & UFP & VFP & SFP & TFP & ZFP & HFP & IFP & TightX & TightY & TightU & TightS &
      ValH & ValI & BoundH & BoundI & FP).
  assert (RFP : Mem.range_perm mp br 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact RF|exact FP|];intro pos.
    unfold mixed_finite_difference_frame,mixed_prepare_frame;
      repeat split;try (left;congruence);congruence. }
  assert (HAP : (mixed_preparation_temps le)!_a=Some (Vptr bp Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HA. }
  assert (HRP : (mixed_preparation_temps le)!_r=Some (Vptr bp Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HR. }
  assert (HNP : (mixed_preparation_temps le)!_rzr=Some (Vptr br Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HN. }
  destruct (exec_mixed_equal_ratio_return e (mixed_preparation_temps le) mp bp bh bi br x y z
    (mixed_h_words x z u) (mixed_i_words y z v) HAP HRP HNP EH EI E0N ED
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    (double_tight_loose _ TightX) (double_tight_loose _ TightY) BZ BoundH BoundI BY H0 I0
    FlagAP XP YP ZP H I PFP HFP IFP RFP)
    as (mf & CR & XO & YO & ZO & FlagO & PFO & BXO & BYO & BZO & HFO & IFO & RY & RFO & FR).
  assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_equal_free AFP FR).
  assert (UFO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_equal_free UFP FR).
  assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_equal_free VFP FR).
  assert (SFO : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_equal_free SFP FR).
  assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_equal_free TFP FR).
  assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_equal_free ZFP FR).
  exists mf;split.
  - rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|exact CR].
  - do 18 (split;[assumption|]).
    eapply lframe_trans.
    + eapply lframe_implies;[exact FP|].
      intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & NR) HV.
      unfold mixed_finite_difference_frame,mixed_prepare_frame;
        repeat split;try assumption;left;assumption.
    + eapply lframe_implies;[exact FR|].
      intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & NR) HV;repeat split;assumption.
Qed.

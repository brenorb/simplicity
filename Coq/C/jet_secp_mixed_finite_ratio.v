(** Entire original finite mixed-addition body with a non-NULL ratio pointer,
    for both H outcomes and, when H is zero, both I outcomes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_statement_prefix C.jet_secp_mixed_preparation C.jet_secp_mixed_finite_prefix
  C.jet_secp_mixed_difference C.jet_secp_mixed_zero C.jet_secp_mixed_zero_branch
  C.jet_secp_mixed_zero_return C.jet_secp_mixed_finite_return C.jet_secp_mixed_finite_body
  C.jet_secp_mixed_equal_ratio C.jet_secp_mixed_ratio_branches C.jet_secp_mixed_nonzero_ratio
  C.jet_secp_mixed_nonzero_tail C.jet_secp_double_coordinate_numeric C.jet_secp_double_all_calls
  C.jet_secp_field_read_preservation C.jet_secp_double_var_owned C.jet_secp_field_zero_owned
  C.jet_secp_double_var_ratio.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words mixed_difference_words.

Definition mixed_finite_ratio_words x y z u v : nat -> int64 :=
  if Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0
  then mixed_zero_words (mixed_i_words y z v) y else mixed_h_words x z u.

Local Ltac keep_return_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_return_free HF Frame :=
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

Theorem exec_mixed_zero_head_return_ratio e le m bp bh bi br x y z h i :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None ->
  e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
  bp<>bh -> bp<>bi -> bh<>bi -> bp<>br -> bh<>br -> bi<>br ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  square_input_bounds h -> square_input_bounds i ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  radix_value h mod feP=0 ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_zero_head E0 (mixed_zero_return_temps le i) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
  fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
  fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf bi 0 (words5 i) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
  square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
  square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
  fe_at mf br 0 (words5 (mixed_zero_words i y)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi /\ bx<>br) m mf.
Proof.
  intros HA HR HN EH EI EN ED EF ES SPH SPI SHI SPR SHR SIR BX BY BZ BH BI Tight HZ Flag X Y Z H I PF HF IF RF.
  destruct (exec_mixed_zero_call false h e le m bh EH EN BH H HF)
    as (mh & CH & HH & HFH & FH).
  assert (VH : field_zero_result h=Int.one) by (unfold field_zero_result;rewrite HZ;reflexivity).
  rewrite VH in CH.
  set (lh := PTree.set _t'2 (Vint Int.one) le).
  assert (HAH : lh!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HA).
  assert (HRH : lh!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HR).
  assert (HNH : lh!_rzr=Some (Vptr br Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HN).
  assert (XH : fe_at mh bp 0 (words5 x)) by (keep_return_field X FH).
  assert (YH : fe_at mh bp 40 (words5 y)) by (keep_return_field Y FH).
  assert (ZH : fe_at mh bp 80 (words5 z)) by (keep_return_field Z FH).
  assert (IH : fe_at mh bi 0 (words5 i)) by (keep_return_field I FH).
  assert (PFH : Mem.range_perm mh bp 0 128 Cur Freeable) by (keep_return_free PF FH).
  assert (IFH : Mem.range_perm mh bi 0 40 Cur Freeable) by (keep_return_free IF FH).
  assert (RFH : Mem.range_perm mh br 0 40 Cur Freeable) by (keep_return_free RF FH).
  assert (FlagH : Mem.load Mint32 mh bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FH Mint32 bp 120);[exact Flag| |intros pos HP;exact SPH].
    eapply Mem.perm_valid_block;apply (PF 0);lia. }
  assert (Branch : exists mf,
    Clight2.exec_stmt secp_ge e lh mh mixed_zero_branch E0 (PTree.set _t'1 (Vint (field_zero_result i)) lh) mf (Out_return None) /\
    fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
    fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
    fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
    Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\ fe_at mf bi 0 (words5 i) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
    square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
    square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
    square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
    fe_at mf br 0 (words5 (mixed_zero_words i y)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
    lframe (fun bx _=>bx<>bp /\ bx<>bi /\ bx<>br) mh mf).
  { unfold mixed_zero_words,mixed_zero_flag,field_zero_result.
    destruct (Z.eqb (radix_value i mod feP) 0) eqn:HI.
    - apply Z.eqb_eq in HI.
      destruct (exec_mixed_equal_ratio e lh mh bp bi br x y z i HAH HRH HNH EI EN ED SPI SPR SIR
        BX BY BZ BI Tight HI FlagH XH YH ZH IH PFH IFH RFH)
        as (mf & CI & XO & YO & ZO & FlagO & IO & PFO & IFO & BXO & BYO & BZO & RY & RFO & FI).
      exists mf;repeat (first [assumption|split]).
    - apply Z.eqb_neq in HI.
      destruct (exec_mixed_inverse_branch_ratio e lh mh bp bi br i HRH HNH EI EN EF ES SPI SPR SIR BI HI IH PFH IFH RFH)
        as (mf & CI & XO & YO & ZO & FlagO & IO & PFO & IFO & RZ & RFO & FI).
      exists mf;repeat (first [assumption|exact square_zero_bounds|split]). }
  destruct Branch as (mf & CB & XO & YO & ZO & FlagO & IO & PFO & IFO & BXO & BYO & BZO & RO & RFO & FB).
  assert (HO : fe_at mf bh 0 (words5 h)) by (keep_return_field HH FB).
  assert (HFO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_return_free HFH FB).
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi /\ bx<>br) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FH|];intros bx pos (NP & NH & NI & NR) HV;exact NH.
    - eapply lframe_implies;[exact FB|];intros bx pos (NP & NH & NI & NR) HV;repeat split;assumption. }
  exists mf;split.
  - change (Clight2.exec_stmt secp_ge e le m
      (Ssequence (mixed_zero_call false) (Sifthenelse (Etempvar _t'2 tint) mixed_zero_branch Sskip)) E0
      (mixed_zero_return_temps le i) mf (Out_return None)).
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mh) (le1:=lh);[exact CH|].
    eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
    + apply eval_Etempvar;unfold lh;apply PTree.gss.
    + reflexivity.
    + exact CB.
  - repeat (first [assumption|split]).
Qed.

Local Ltac keep_return_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_finite_zero_body_ratio e le m bp ba bu bv bs bt bz bh bi br x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None ->
  e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
  NoDup [br;bh;bi;bp;ba;bu;bv;bs;bt;bz] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  radix_value (mixed_h_words x z u) mod feP=0 ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_zero_return_temps (mixed_preparation_temps le) (mixed_i_words y z v)) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (mixed_zero_words (mixed_i_words y z v) (double_output_x_words x y))) /\
  fe_at mf bp 40 (words5 (mixed_zero_words (mixed_i_words y z v) (double_output_y_words x y))) /\
  fe_at mf bp 80 (words5 (mixed_zero_words (mixed_i_words y z v) (double_output_z_words y z))) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag (mixed_i_words y z v) y z)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (mixed_zero_words (mixed_i_words y z v) (double_output_x_words x y)) /\
  square_input_bounds (mixed_zero_words (mixed_i_words y z v) (double_output_y_words x y)) /\
  square_input_bounds (mixed_zero_words (mixed_i_words y z v) (double_output_z_words y z)) /\
  fe_at mf br 0 (words5 (mixed_zero_words (mixed_i_words y z v) y)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx pos=>mixed_finite_return_frame bp ba bu bv bs bt bz bh bi bx pos /\ bx<>br) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI EW EM EQ EN EA E0N ED EF ESI Sep FlagA FlagB BX BY BZ BU BV H0
    X Y Z U V PF AF UF VF SF TF ZF HF IF RF.
  assert (SepP : NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz]).
  { apply NoDup_cons_iff in Sep;exact (proj2 Sep). }
  pose proof Sep as Sep0;separate_ratio_blocks Sep0.
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
  destruct (exec_mixed_zero_head_return_ratio e (mixed_preparation_temps le) mp bp bh bi br x y z
    (mixed_h_words x z u) (mixed_i_words y z v) HAP HRP HNP EH EI E0N ED EF ESI
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    (double_tight_loose _ TightX) (double_tight_loose _ TightY) BZ BoundH BoundI BY H0
    FlagAP XP YP ZP H I PFP HFP IFP RFP)
    as (mf & CR & XO & YO & ZO & FlagO & HO & IO & PFO & HFO & IFO & BXO & BYO & BZO & RO & RFO & FR).
  assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_return_owned AFP FR).
  assert (UFO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_return_owned UFP FR).
  assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_return_owned VFP FR).
  assert (SFO : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_return_owned SFP FR).
  assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_return_owned TFP FR).
  assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_return_owned ZFP FR).
  exists mf;split.
  - rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|].
    rewrite mixed_zero_source;eapply exec_Sseq_2;[exact CR|discriminate].
  - do 18 (split;[assumption|]).
    eapply lframe_trans.
    + eapply lframe_implies;[exact FP|].
      intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & NR) HV.
      unfold mixed_finite_difference_frame,mixed_prepare_frame;
        repeat split;try assumption;left;assumption.
    + eapply lframe_implies;[exact FR|].
      intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & NR) HV;repeat split;assumption.
Qed.

Local Ltac separate_finite_blocks Sep := separate_ratio_blocks Sep.
Local Ltac keep_finite_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac outside_preparation :=
  unfold mixed_finite_difference_frame,mixed_prepare_frame;
    repeat split;try (left;congruence);congruence.

Theorem exec_mixed_finite_body_ratio e le m bp ba bu bv bs bt bz bh bi b2 b3 bk br x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk;br] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_finite_body_temps le x y z u v) mf (mixed_finite_body_out x z u) /\
  fe_at mf bp 0 (words5 (mixed_finite_x_words x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_finite_y_words x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_finite_z_words x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_finite_flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
  square_input_bounds (mixed_finite_x_words x y z u v) /\ square_input_bounds (mixed_finite_y_words x y z u v) /\
  square_input_bounds (mixed_finite_z_words x y z u v) /\
  fe_at mf br 0 (words5 (mixed_finite_ratio_words x y z u v)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx pos=>mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk bx pos /\ bx<>br) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF ESI Sep FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK RF.
  pose proof Sep as Sep0;separate_finite_blocks Sep0.
  assert (SepP : NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz]) by sep_goal.
  assert (SepZ : NoDup [br;bh;bi;bp;ba;bu;bv;bs;bt;bz]) by sep_goal.
  assert (SepN : NoDup [bp;bh;b2;b3;bk;bu;bi;bs;br]) by sep_goal.
  unfold mixed_finite_body_temps,mixed_finite_body_out,mixed_finite_x_words,mixed_finite_y_words,
    mixed_finite_z_words,mixed_finite_flag,mixed_finite_ratio_words.
  destruct (Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0) eqn:HC.
  - apply Z.eqb_eq in HC.
    destruct (exec_mixed_finite_zero_body_ratio e le m bp ba bu bv bs bt bz bh bi br x y z u v
      HA HB HR HN EU EV ES ET EZ EH EI EW EM EQ EN EA E0N ED EF ESI SepZ FlagA FlagB BX BY BZ BU BV HC
      X Y Z U V PF AF UF VF SF TF ZF HF IF RF)
      as (mf & CB & XO & YO & ZO & FlagO & PFO & AFO & UFO & VFO & SFO & TFO & ZFO & HFO & IFO &
        BXO & BYO & BZO & RO & RFO & FB).
    assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_finite_owned F2 FB).
    assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_finite_owned F3 FB).
    assert (FKO : Mem.range_perm mf bk 0 40 Cur Freeable) by (keep_finite_owned FK FB).
    assert (Frame : lframe (fun bx pos=>mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk bx pos /\ bx<>br) m mf).
    { eapply lframe_implies;[exact FB|];intros bx pos ((FF & N2 & N3 & NK) & NR) HV;exact (conj FF NR). }
    exists mf;repeat (first [assumption|split]).
  - apply Z.eqb_neq in HC.
    destruct (exec_mixed_finite_difference e le m bp ba bu bv bs bt bz bh bi x y z u v
      HA HB EU EV ES ET EZ EH EI EW EM EQ EN EA SepP FlagA FlagB BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF)
      as (mp & CP & XP & YP & ZP & UP & VP & U1 & U2 & S1 & S2 & Z12 & H & I & FlagAP & FlagBP &
        PFP & AFP & UFP & VFP & SFP & TFP & ZFP & HFP & IFP & TightX & TightY & TightU & TightS & ValH & ValI & BoundH & BoundI & FP).
    assert (F2P : Mem.range_perm mp b2 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact F2|exact FP|];intro pos;outside_preparation. }
    assert (F3P : Mem.range_perm mp b3 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact F3|exact FP|];intro pos;outside_preparation. }
    assert (FKP : Mem.range_perm mp bk 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FK|exact FP|];intro pos;outside_preparation. }
    assert (RFP : Mem.range_perm mp br 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact RF|exact FP|];intro pos;outside_preparation. }
    assert (HAP : (mixed_preparation_temps le)!_a=Some (Vptr bp Ptrofs.zero)).
    { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HA. }
    assert (HRP : (mixed_preparation_temps le)!_r=Some (Vptr bp Ptrofs.zero)).
    { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HR. }
    assert (HNP : (mixed_preparation_temps le)!_rzr=Some (Vptr br Ptrofs.zero)).
    { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HN. }
    destruct (exec_mixed_nonzero_tail_ratio e (mixed_preparation_temps le) mp bp bh b2 b3 bk bu bi bs br x y z
      (mixed_h_words x z u) x (mixed_i_words y z v) y HAP HRP HNP EH E2 E3 EK EU EI ES E0N EM EQ EN EA SepN
      BZ BoundH (double_tight_loose _ TightX) BoundI (double_tight_loose _ TightY) HC XP YP ZP H U1 I S1
      PFP HFP F2P F3P FKP UFP IFP SFP RFP)
      as (mf & CN & XO & YO & ZO & FlagO & PFO & HFO & F2O & F3O & FKO & UFO & IFO & SFO & BXO & BYO & BZO & RO & RFO & FN).
    assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_finite_owned AFP FN).
    assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_finite_owned VFP FN).
    assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_finite_owned TFP FN).
    assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_finite_owned ZFP FN).
    assert (Frame : lframe (fun bx pos=>mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk bx pos /\ bx<>br) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FP|];intros bx pos (((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) & NR) HV.
        unfold mixed_finite_difference_frame,mixed_prepare_frame;repeat split;try assumption;left;assumption.
      - eapply lframe_implies;[exact FN|];intros bx pos (((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) & NR) HV.
        unfold mixed_nonzero_tail_ratio_frame,mixed_nonzero_tail_frame;repeat split;try assumption;left;exact NP. }
    exists mf;split.
    + rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|exact CN].
    + repeat (first [assumption|split]).
Qed.

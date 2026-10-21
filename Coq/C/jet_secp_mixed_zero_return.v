(** Actual H test followed by either I-dependent early return. Every call is
    derived from owned storage; neither branch execution nor its result is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_field_zero_owned C.jet_secp_mixed_zero C.jet_secp_mixed_zero_branch
  C.jet_secp_mixed_difference C.jet_secp_double_var_owned C.jet_secp_double_all_calls.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_zero_words i (w : nat -> int64) :=
  if Z.eqb (radix_value i mod feP) 0 then w else fun _ : nat => Int64.zero.
Definition mixed_zero_flag i y z :=
  if Z.eqb (radix_value i mod feP) 0 then double_var_zflag y z else Int.one.
Definition mixed_zero_return_temps le i :=
  PTree.set _t'1 (Vint (field_zero_result i)) (PTree.set _t'2 (Vint Int.one) le).

Local Ltac keep_return_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_return_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_zero_return e le m bp bh bi x y z h i :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
  bp<>bh -> bp<>bi -> bh<>bi ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  square_input_bounds h -> square_input_bounds i -> radix_value h mod feP=0 ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_after_difference E0 (mixed_zero_return_temps le i) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
  fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
  fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf bi 0 (words5 i) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
  square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
  square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
  lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi) m mf.
Proof.
  intros HA HR HN EH EI EN ED EF SPH SPI SHI BX BY BZ BH BI HZ Flag X Y Z H I PF HF IF.
  destruct (exec_mixed_zero_call false h e le m bh EH EN BH H HF)
    as (mh & CH & HH & HFH & FH).
  assert (VH : field_zero_result h=Int.one) by (unfold field_zero_result;rewrite HZ;reflexivity).
  rewrite VH in CH.
  set (lh := PTree.set _t'2 (Vint Int.one) le).
  assert (HAH : lh!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HA).
  assert (HRH : lh!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HR).
  assert (HNH : lh!_rzr=Some (Vlong Int64.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HN).
  assert (XH : fe_at mh bp 0 (words5 x)) by (keep_return_field X FH).
  assert (YH : fe_at mh bp 40 (words5 y)) by (keep_return_field Y FH).
  assert (ZH : fe_at mh bp 80 (words5 z)) by (keep_return_field Z FH).
  assert (IH : fe_at mh bi 0 (words5 i)) by (keep_return_field I FH).
  assert (PFH : Mem.range_perm mh bp 0 128 Cur Freeable) by (keep_return_free PF FH).
  assert (IFH : Mem.range_perm mh bi 0 40 Cur Freeable) by (keep_return_free IF FH).
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
    lframe (fun bx _=>bx<>bp /\ bx<>bi) mh mf).
  { unfold mixed_zero_words,mixed_zero_flag,field_zero_result.
    destruct (Z.eqb (radix_value i mod feP) 0) eqn:HI.
    - apply Z.eqb_eq in HI.
      exact (exec_mixed_equal_branch e lh mh bp bi x y z i HAH HRH HNH EI EN ED SPI BX BY BZ BI HI
        FlagH XH YH ZH IH PFH IFH).
    - apply Z.eqb_neq in HI.
      destruct (exec_mixed_inverse_branch e lh mh bp bi i HRH HNH EI EN EF SPI BI HI IH PFH IFH)
        as (mf & CI & XO & YO & ZO & FlagO & IO & PFO & IFO & FI).
      exists mf;repeat (first [assumption|exact square_zero_bounds|split]). }
  destruct Branch as (mf & CB & XO & YO & ZO & FlagO & IO & PFO & IFO & BXO & BYO & BZO & FB).
  assert (HO : fe_at mf bh 0 (words5 h)) by (keep_return_field HH FB).
  assert (HFO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_return_free HFH FB).
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FH|];intros bx pos (NP & NH & NI) HV;exact NH.
    - eapply lframe_implies;[exact FB|];intros bx pos (NP & NH & NI) HV;split;assumption. }
  exists mf;split.
  - rewrite mixed_zero_source;eapply exec_Sseq_2;[|discriminate].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mh) (le1:=lh);[exact CH|].
    eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
    + apply eval_Etempvar;unfold lh;apply PTree.gss.
    + reflexivity.
    + exact CB.
  - repeat (first [assumption|split]).
Qed.

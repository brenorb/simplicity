(** Complete original gej_double statement body: real flag load/store followed
    by all arithmetic, with all post-store facts derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
  C.jet_secp_double_statements C.jet_secp_double_flag C.jet_secp_double_body_owned
  C.jet_secp_double_all_calls C.jet_secp_double_prefix C.jet_secp_curve_frame
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_double_body_owned le x y z m ba bs bl bt flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  Mem.load Mint32 m ba 120=Some (Vint flag) ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m (fn_body f_secp256k1_gej_double)
    E0 (PTree.set _t'1 (Vint flag) le) mf Out_normal /\
  fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
  fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
  fe_at mf ba 80 (words5 (double_output_z_words y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  lframe (fun b pos => double_work_frame ba bs bl b pos /\ b<>bt) m mf.
Proof.
  intros HA HR HLoad BX BY BZ HAS HAL HAT HSL HST HLT HX HY HZ HFA HFS HFL HFT.
  destruct (double_flag_copy_owned (double_helper_env bl bs bt) le x y z m ba flag
    HA HR HLoad HX HY HZ HFA) as (mi & HFlag & XI & YI & ZI & AFI & FI).
  pose proof (curve_keep_free _ m mi bs 40 ltac:(lia) HFS FI ltac:(intro pos;left;congruence)) as SFI.
  pose proof (curve_keep_free _ m mi bl 40 ltac:(lia) HFL FI ltac:(intro pos;left;congruence)) as LFI.
  pose proof (curve_keep_free _ m mi bt 40 ltac:(lia) HFT FI ltac:(intro pos;left;congruence)) as TFI.
  assert (HA' : (PTree.set _t'1 (Vint flag) le)!_a=Some (Vptr ba Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HA).
  assert (HR' : (PTree.set _t'1 (Vint flag) le)!_r=Some (Vptr ba Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HR).
  destruct (exec_double_arithmetic_owned (PTree.set _t'1 (Vint flag) le) x y z mi ba bs bl bt
    HA' HR' BX BY BZ HAS HAL HAT HSL HST HLT XI YI ZI AFI SFI LFI TFI)
    as (mf & HArith & XF & YF & ZF & AF & SF & LF & TF & BXF & BYF & BZF & FF).
  exists mf;split.
  - rewrite double_helper_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=PTree.set _t'1 (Vint flag) le);
      [exact HFlag|exact HArith].
  - split;[exact XF|];split;[exact YF|];split;[exact ZF|].
    split;[exact AF|];split;[exact SF|];split;[exact LF|];split;[exact TF|].
    split;[exact BXF|];split;[exact BYF|];split;[exact BZF|].
    eapply lframe_trans;[|exact FF].
    eapply lframe_implies;[exact FI|]. intros b pos [(NA & NS & NL) NT] HV;left;exact NA.
Qed.

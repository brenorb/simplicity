(** Original non-NULL double_var ratio path.  The ratio storage is distinct
    from the point and may initially be uninitialized.  This is helper
    execution, not yet a whole-public mixed-addition counterexample. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_double_var_statements C.jet_secp_double_var_owned
  C.jet_secp_double_function C.jet_secp_double_all_calls C.jet_secp_point_normalizes_zero
  C.jet_secp_point_write_run C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_curve_frame C.jet_secp_local_regions
  C.jet_secp_field_read_preservation C.jet_secp_mixed_copy_weak
  C.jet_secp_field_copy_owned C.jet_secp_field_weak_tight
  C.jet_secp_curve_statements C.jet_secp_double_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_var_ratio_copy := Sassign
  (Ederef (Etempvar _rzr (tptr curve_fe_type)) curve_fe_type)
  (double_point_field _a _y curve_fe_type).
Definition double_var_ratio_weak := curve_call _secp256k1_fe_normalize_weak
  f_secp256k1_fe_normalize_weak None [Etempvar _rzr (tptr curve_fe_type)].
Lemma double_var_ratio_source : double_var_tail = Ssequence
  (Sifthenelse double_var_null_test
    (Ssequence double_var_ratio_copy double_var_ratio_weak) Sskip)
  double_var_post_ratio.
Proof. reflexivity. Qed.

Lemma eval_double_var_nonnull_test e le m br :
  le!_rzr=Some (Vptr br Ptrofs.zero) ->
  Mem.valid_pointer m br 0=true ->
  eval_expr secp_ge e le m double_var_null_test (Vint Int.one).
Proof.
  intros HR HV;unfold double_var_null_test.
  eapply eval_Ebinop with (v1:=Vptr br Ptrofs.zero) (v2:=Vlong Int64.zero).
  - apply eval_Etempvar;exact HR.
  - eapply eval_Ecast with (v1:=Vint Int.zero);[constructor|reflexivity].
  - change (option_map Val.of_bool
      (if (Mem.valid_pointer m br 0 || Mem.valid_pointer m br (-1))%bool
       then Some true else None)=Some (Vint Int.one)).
    rewrite HV;reflexivity.
Qed.

Definition double_var_ratio_temps ba br := PTree.set _rzr (Vptr br Ptrofs.zero)
  (PTree.set _a (Vptr ba Ptrofs.zero) (PTree.set _r (Vptr ba Ptrofs.zero)
    (create_undef_temps (fn_temps f_secp256k1_gej_double_var)))).
Lemma double_var_ratio_entry m ba br :
  function_entry2 secp_ge f_secp256k1_gej_double_var
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero]
    m empty_env (double_var_ratio_temps ba br) m.
Proof.
  destruct (fn_okb_true _ double_var_function_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Theorem exec_double_var_ratio_owned e le m ba br y :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_secp256k1_fe_normalize_weak=None -> ba<>br ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m
    (Sifthenelse double_var_null_test
      (Ssequence double_var_ratio_copy double_var_ratio_weak) Sskip) E0 le mf Out_normal /\
  fe_at mf br 0 (words5 y) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  fe_at mf ba 40 (words5 y) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
  lframe (fun b _=>b<>br) m mf.
Proof.
  intros HA HR HE HSep BY Y PF RF.
  destruct (exec_field_copy_owned e le m
    (double_point_field _a _y curve_fe_type)
    (Ederef (Etempvar _rzr (tptr curve_fe_type)) curve_fe_type)
    ba 40 br 0 y eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[exact (eval_mixed_a_copy_field e le m ba true HA)|
      apply deref_loc_copy;reflexivity])
    ltac:(apply eval_Ederef;apply eval_Etempvar;exact HR)
    HSep Y ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia) RF)
    as (mc & Copy & YC & PC & FC).
  assert (RFC : Mem.range_perm mc br 0 40 Cur Freeable).
  { intros pos HP;apply (proj2 (PC br pos Cur Freeable));apply RF;exact HP. }
  destruct (eval_field_weak_tight y mc br BY YC RFC)
    as (mf & Weak & YF & RFF & FW).
  assert (Frame : lframe (fun b _=>b<>br) m mf).
  { eapply lframe_trans;[|exact FW].
    eapply lframe_implies;[exact FC|];intros b pos HN HV;left;exact HN. }
  exists mf;split.
  - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
    + apply eval_double_var_nonnull_test with (br:=br);[exact HR|].
      apply Mem.valid_pointer_nonempty_perm.
      eapply Mem.perm_implies;[apply (RF 0);lia|constructor].
    + reflexivity.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le).
      * exact Copy.
      * unfold double_var_ratio_weak.
        eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero]) (v:=Vundef).
        -- unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
        -- exact HE.
        -- eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|constructor].
        -- exact Weak.
  - split;[exact YF|];split;[exact RFF|];split.
    + eapply field_at_lframe;[exact Y|exact Frame|];intros;exact HSep.
    + split;[|exact Frame].
      eapply curve_keep_free;[lia|exact PF|exact Frame|];intros;exact HSep.
Qed.

(** Positioned Y covers the output of the public field reader.  This helper
    does not assert that other legitimate public inputs may be excluded. *)
Theorem eval_double_var_finite_ratio x y z m ba br :
  ba<>br -> square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
  fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
  fe_at mf ba 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf ba 120=Some (Vint (double_var_zflag y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  fe_at mf br 0 (words5 y) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun b _=>b<>ba /\ b<>br) m mf.
Proof.
  intros Sep BX BY BZ Tight Flag X Y Z PF RF.
  set (le0 := double_var_ratio_temps ba br).
  set (le1 := PTree.set _t'2 (Vint Int.zero) le0).
  assert (HA : le1!_a=Some (Vptr ba Ptrofs.zero)) by reflexivity.
  assert (HR : le1!_r=Some (Vptr ba Ptrofs.zero)) by reflexivity.
  assert (HN : le1!_rzr=Some (Vptr br Ptrofs.zero)) by reflexivity.
  destruct (exec_double_var_ratio_owned empty_env le1 m ba br y
    HA HN eq_refl Sep Tight Y PF RF)
    as (mr & Ratio & RY & RFR & YR & PFR & FR).
  assert (XR : fe_at mr ba 0 (words5 x)).
  { eapply field_at_lframe;[exact X|exact FR|];intros;exact Sep. }
  assert (ZR : fe_at mr ba 80 (words5 z)).
  { eapply field_at_lframe;[exact Z|exact FR|];intros;exact Sep. }
  assert (FlagR : Mem.load Mint32 mr ba 120=Some (Vint Int.zero)).
  { rewrite (proj1 FR Mint32 ba 120);[exact Flag| |intros;exact Sep].
    eapply Mem.perm_valid_block;apply (PF 0);lia. }
  destruct (eval_double_function x y z mr ba Int.zero BX BY BZ FlagR XR YR ZR PFR)
    as (md & CD & XD & YD & ZD & FD & BXD & BYD & BZD & HD).
  destruct (eval_point_normalizes_zero PointZ (double_output_z_words y z) md ba BZD ZD FD)
    as (mz & CZ & ZZ & FZ & HZF).
  assert (XZ : fe_at mz ba 0 (words5 (double_output_x_words x y))).
  { eapply curve_keep_field_range;[reflexivity|exact XD|exact HZF|];
    intros pos HP;right;left;change (pos<80);lia. }
  assert (YZ : fe_at mz ba 40 (words5 (double_output_y_words x y))).
  { eapply curve_keep_field_range;[reflexivity|exact YD|exact HZF|];
    intros pos HP;right;left;change (pos<80);lia. }
  destruct (double_var_store_flag (double_output_x_words x y) (double_output_y_words x y)
    (double_output_z_words y z) mz ba (double_var_zflag y z) XZ YZ ZZ FZ)
    as (mf & HS & LF & XF & YF & ZF & FF & HSF).
  assert (FDbl : lframe (fun b _=>b<>ba) mr mf).
  { eapply lframe_trans;[exact HD|].
    eapply lframe_trans.
    - eapply lframe_implies;[exact HZF|];intros b pos HO HV;left;exact HO.
    - eapply lframe_implies;[exact HSF|];intros b pos HO HV;left;exact HO. }
  assert (RYF : fe_at mf br 0 (words5 y)).
  { eapply field_at_lframe;[exact RY|exact FDbl|];intros;congruence. }
  assert (RFF : Mem.range_perm mf br 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact RFR|exact FDbl|];intros;congruence. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env) (le1:=le0)
      (le2:=PTree.set _t'1 (Vint (double_var_zflag y z)) le1)
      (m1:=m) (m2:=mf) (out:=Out_normal).
    + exact (double_var_ratio_entry m ba br).
    + rewrite double_var_source.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le1).
      * apply exec_double_var_head_finite with (ba:=ba);[reflexivity|exact Flag].
      * rewrite double_var_ratio_source.
        eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le1);[exact Ratio|].
        exact (exec_double_var_post_ratio_from_calls empty_env le1 mr md mz mf ba
          (double_var_zflag y z) HA HR eq_refl eq_refl CD CZ HS).
    + reflexivity.
    + reflexivity.
  - do 10 (split;[assumption|]).
    eapply lframe_trans.
    + eapply lframe_implies;[exact FR|];intros b pos (NA & NR) HV;exact NR.
    + eapply lframe_implies;[exact FDbl|];intros b pos (NA & NR) HV;exact NA.
Qed.

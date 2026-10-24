(** Execute the original SWU joint-denominator setup from caller storage.
    Keep the original 7+1 expression, magnitude-3 negation, and struct copy.
    The prefix ends with skip so its execution composes with the unchanged
    suffix using exec_statement_prefix_then_last. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Cop
  Integers Memory Values Events Maps.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_swu_startup C.jet_secp_swu_initial C.jet_secp_fe_math
  C.jet_secp_field_copy_owned C.jet_secp_field_mul_small C.jet_secp_field_add_int
  C.jet_secp_field_negate_magnitude C.jet_secp_square_columns
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_fns C.jet_secp_closed_helpers C.jet_clight_internal_frame
  C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_copy_x3d := Sassign (Evar _x3d curve_fe_type) (Evar _wd curve_fe_type).
Definition swu_scale_x3d := curve_call _secp256k1_fe_mul_int f_secp256k1_fe_mul_int None
  [curve_local_address _x3d;Econst_int (Int.repr 3) tint].
Definition swu_negate_x3d := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
  [curve_local_address _x3d;curve_local_address _x3d;Econst_int (Int.repr 3) tint].
Definition swu_add8_wd := curve_call _secp256k1_fe_add_int f_secp256k1_fe_add_int None
  [curve_local_address _wd;Ebinop Oadd (Econst_int (Int.repr 7) tint)
    (Econst_int (Int.repr 1) tint) tint].
Definition swu_joint_setup_statements :=
  [swu_copy_x3d;swu_scale_x3d;swu_negate_x3d;swu_add8_wd].
Definition swu_joint_setup := statement_sequence swu_joint_setup_statements Sskip.
Definition swu_after_joint_setup := match swu_after_initial with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest)))=>rest | _=>Sskip end.
Lemma swu_joint_setup_source : swu_after_initial=
  statement_sequence swu_joint_setup_statements swu_after_joint_setup.
Proof. reflexivity. Qed.
Lemma swu_joint_setup_closed : closed_stmtb secp_closed_helpers swu_joint_setup=true.
Proof. vm_compute;reflexivity. Qed.

Lemma exec_swu_copy_x3d e le m bwd bx w :
  e!_wd=Some (bwd,curve_fe_type) -> e!_x3d=Some (bx,curve_fe_type) -> bwd<>bx ->
  fe_at m bwd 0 (words5 w) -> Mem.range_perm m bx 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_copy_x3d E0 le mf Out_normal /\
  fe_at mf bx 0 (words5 w) /\
  (forall b pos k p,Mem.perm mf b pos k p<->Mem.perm m b pos k p) /\
  lframe (fun b pos=>b<>bx \/ pos<0 \/ 40<=pos) m mf.
Proof.
  intros W X Ne Input Free;unfold swu_copy_x3d.
  eapply exec_field_copy_owned with (bs:=bwd) (sbase:=0) (bd:=bx) (dbase:=0);
    [reflexivity|reflexivity| | |exact Ne|exact Input|lia|exists 0;reflexivity|
     change (40<=18446744073709551615);lia|exact Free].
  - eapply eval_Elvalue;[apply eval_Evar_local;exact W|apply deref_loc_copy;reflexivity].
  - apply eval_Evar_local;exact X.
Qed.
Lemma exec_swu_scale_call e le m mf bx :
  e!_secp256k1_fe_mul_int=None -> e!_x3d=Some (bx,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul_int)
    [Vptr bx Ptrofs.zero;Vint (Int.repr 3)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_scale_x3d E0 le mf Out_normal.
Proof.
  intros Fun X Call;unfold swu_scale_x3d;eapply exec_curve_call with
    (vargs:=[Vptr bx Ptrofs.zero;Vint (Int.repr 3)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact X|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_negate_call e le m mf bx :
  e!_secp256k1_fe_negate=None -> e!_x3d=Some (bx,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (Int.repr 3)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_negate_x3d E0 le mf Out_normal.
Proof.
  intros Fun X Call;unfold swu_negate_x3d;eapply exec_curve_call with
    (vargs:=[Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (Int.repr 3)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact X|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact X|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_add8_call e le m mf bwd :
  e!_secp256k1_fe_add_int=None -> e!_wd=Some (bwd,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr bwd Ptrofs.zero;Vint (Int.repr 8)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_add8_wd E0 le mf Out_normal.
Proof.
  intros Fun W Call;unfold swu_add8_wd;eapply exec_curve_call with
    (vargs:=[Vptr bwd Ptrofs.zero;Vint (Int.repr 8)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact W|reflexivity|].
    eapply eval_Econs;
      [eapply eval_Ebinop;[constructor|constructor|reflexivity]|reflexivity|constructor].
  - exact Call.
Qed.

Definition swu_setup_x3d w := negate_mag_words (Int.repr 3) (mul_small_words (Int.repr 3) w).
Definition swu_setup_wd w := add_int_words (Int.repr 8) w.
Theorem exec_swu_joint_setup e le m bwd bx w : plain_env e ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add_int=None ->
  e!_wd=Some (bwd,curve_fe_type) -> e!_x3d=Some (bx,curve_fe_type) -> bwd<>bx -> swu_startup m ->
  mul_small_input_bounds w -> fe_at m bwd 0 (words5 w) ->
  Mem.range_perm m bwd 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_joint_setup E0 le mf Out_normal /\
  fe_at mf bwd 0 (words5 (swu_setup_wd w)) /\ fe_at mf bx 0 (words5 (swu_setup_x3d w)) /\
  Mem.range_perm mf bwd 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  radix_value (swu_setup_wd w)=radix_value w+8 /\
  radix_value (swu_setup_x3d w)=8*feP-3*radix_value w /\
  square_input_bounds (swu_setup_wd w) /\ square_input_bounds (swu_setup_x3d w) /\ swu_startup mf /\
  lframe (fun b _=>b<>bwd /\ b<>bx) m mf /\ readonly_preserved m mf.
Proof.
  intros Plain EM EN EA EW EX Ne Ready Bounds Input FW FX.
  destruct (exec_swu_copy_x3d e le m bwd bx w EW EX Ne Input FX) as (mc & Copy & XC & PC & FC).
  assert (FXC:Mem.range_perm mc bx 0 40 Cur Freeable)
    by (intros pos Range;apply PC;apply FX;exact Range).
  assert (FWC:Mem.range_perm mc bwd 0 40 Cur Freeable)
    by (intros pos Range;apply PC;apply FW;exact Range).
  assert (WC:fe_at mc bwd 0 (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact Input|exact FC|];intros;left;exact Ne. }
  destruct (eval_field_mul_small_from_storage (Int.repr 3) w mc bx
    ltac:(change (0<=3<=7);lia) Bounds XC FXC)
    as (mm & Mul & XM & FXM & MulValue & MulBounds & FM).
  destruct (eval_negate_mag_bounded (Int.repr 3) (mul_small_words (Int.repr 3) w) mm bx
    ltac:(change (0<=3<=7);lia)
    (negate_mag_scaled_input (Int.repr 3) w ltac:(change (0<=3<=7);lia) Bounds) XM FXM)
    as (mn & Neg & XN & FXN & NegValue & NegBounds & FN).
  assert (WN:fe_at mn bwd 0 (words5 w)).
  { eapply curve_keep_field_range;[reflexivity| |exact FN|];[|intros;exact Ne].
    eapply curve_keep_field_range;[reflexivity|exact WC|exact FM|];intros;exact Ne. }
  assert (FWN:Mem.range_perm mn bwd 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia| |exact FN|];[|intros;exact Ne].
    eapply curve_keep_free;[lia|exact FWC|exact FM|];intros;exact Ne. }
  destruct (eval_field_add_int_small (Int.repr 8) w mn bwd
    ltac:(change (0<=8<=8);lia) Bounds WN FWN)
    as (mf & Add & WF & FWF & AddValue & AddBounds & FA).
  assert (XF:fe_at mf bx 0 (words5 (swu_setup_x3d w))).
  { eapply curve_keep_field_range;[reflexivity|exact XN|exact FA|];intros;congruence. }
  assert (FXF:Mem.range_perm mf bx 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FXN|exact FA|];intros;congruence. }
  assert (Run:Clight2.exec_stmt secp_ge e le m swu_joint_setup E0 le mf Out_normal).
  { unfold swu_joint_setup,swu_joint_setup_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mc);[exact Copy|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mm);
      [eapply exec_swu_scale_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mn);
      [eapply exec_swu_negate_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);
      [eapply exec_swu_add8_call;eassumption|apply exec_Sskip]. }
  assert (Readonly:readonly_preserved m mf) by
    (eapply secp_closed_stmt_preserved;[exact Run|exact Plain|exact swu_joint_setup_closed]).
  change (radix_value (mul_small_words (Int.repr 3) w)=3*radix_value w) in MulValue.
  change (radix_value (swu_setup_x3d w)=8*feP-radix_value (mul_small_words (Int.repr 3) w)) in NegValue.
  rewrite MulValue in NegValue.
  exists mf;split;[exact Run|];split;[exact WF|];split;[exact XF|];split;[exact FWF|];
    split;[exact FXF|];split;[exact AddValue|];split;[exact NegValue|];split;[exact AddBounds|];
    split;[exact NegBounds|];split;[apply (swu_startup_preserved m mf Ready Readonly)|];split;
    [|exact Readonly].
  eapply lframe_trans with (m2:=mc).
  - eapply lframe_implies;[exact FC|];intros b pos [_ NX] _;left;exact NX.
  - eapply lframe_trans with (m2:=mm).
    + eapply lframe_implies;[exact FM|];intros b pos [_ NX] _;exact NX.
    + eapply lframe_trans with (m2:=mn).
      * eapply lframe_implies;[exact FN|];intros b pos [_ NX] _;exact NX.
      * eapply lframe_implies;[exact FA|];intros b pos [NW _] _;exact NW.
Qed.

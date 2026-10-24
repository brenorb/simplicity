(** Original SWU denominator product and in-place fe_inv_var call.
    The CTZ call contract remains explicit, as in the existing original
    inversion proof; internal execution and inverse values are derived. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep
  Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_swu_startup C.jet_secp_swu_initial
  C.jet_secp_swu_joint_setup C.jet_secp_swu_constant_product C.jet_secp_swu_candidates
  C.jet_secp_fe_math C.jet_secp_field_mul_small C.jet_secp_field_add_int
  C.jet_secp_field_negate_magnitude C.jet_secp_square_columns
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_field_product_owned C.jet_secp_curve_mul
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_fe_inverse_var C.jet_secp_fe_inv_prefix C.jet_secp_invert_literal
  C.jet_secp_invert_modinv C.jet_secp_fns C.jet_secp_closed_helpers
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_joint_product := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _jinv;curve_local_address _wd;curve_local_address _x3d].
Definition swu_joint_invert := curve_call _secp256k1_fe_inv_var f_secp256k1_fe_inv_var None
  [curve_local_address _jinv;curve_local_address _jinv].
Definition swu_after_joint_inverse := match swu_after_joint_setup with
  | Ssequence _ (Ssequence _ rest)=>rest | _=>Sskip end.
Definition swu_joint_inverse_statements :=
  swu_joint_setup_statements++[swu_joint_product;swu_joint_invert].
Definition swu_joint_inverse_prefix := statement_sequence swu_joint_inverse_statements Sskip.
Lemma swu_joint_inverse_source : swu_after_joint_setup=
  Ssequence swu_joint_product (Ssequence swu_joint_invert swu_after_joint_inverse).
Proof. reflexivity. Qed.
Lemma swu_joint_inverse_prefix_source : swu_after_initial=
  statement_sequence swu_joint_inverse_statements swu_after_joint_inverse.
Proof. reflexivity. Qed.

Definition swu_joint_words w := point_mul_words (swu_setup_wd w) (swu_setup_x3d w).
Lemma swu_joint_words_value w : mul_small_input_bounds w ->
  radix_value (swu_joint_words w) mod feP=((radix_value w+8)*(-3*radix_value w)) mod feP.
Proof.
  intro Bounds.
  assert (C8:0<=Int.signed (Int.repr 8)<=8) by (change (0<=8<=8);lia).
  assert (C3:0<=Int.signed (Int.repr 3)<=7) by (change (0<=3<=7);lia).
  pose proof (add_int_bounds (Int.repr 8) w C8 Bounds) as WB.
  pose proof (negate_mag_scaled_input (Int.repr 3) w C3 Bounds) as XB.
  pose proof (negate_mag_numeric (Int.repr 3) (mul_small_words (Int.repr 3) w) C3 XB)
    as [XN XBounds].
  destruct (curve_mul_value_bounds (swu_setup_wd w) (swu_setup_x3d w)
    (field_operand_from_bounds _ WB) (field_operand_from_bounds _ XBounds)) as [Value _].
  assert (NoWrap:0<=Int64.unsigned (w 0%nat)+Int.signed (Int.repr 8)<=Int64.max_unsigned).
  { pose proof (Bounds 0%nat ltac:(lia)) as Low;cbn [Nat.eqb] in Low.
    pose proof (Int64.unsigned_range_2 (w 0%nat));change (Int.signed (Int.repr 8)) with 8;
      change Int64.max_unsigned with 18446744073709551615;lia. }
  pose proof (add_int_radix (Int.repr 8) w NoWrap) as WV.
  pose proof (mul_small_radix (Int.repr 3) w C3 Bounds) as XV.
  change (radix_value (swu_setup_wd w)=radix_value w+8) in WV.
  change (radix_value (mul_small_words (Int.repr 3) w)=3*radix_value w) in XV.
  change (radix_value (swu_setup_x3d w)=8*feP-radix_value (mul_small_words (Int.repr 3) w)) in XN.
  rewrite XV in XN;rewrite WV,XN in Value;unfold swu_joint_words;rewrite Value.
  replace ((radix_value w+8)*(8*feP-3*radix_value w)) with
    ((radix_value w+8)*(-3*radix_value w)+(8*(radix_value w+8))*feP) by ring.
  rewrite Z.mod_add by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma swu_joint_inverse_value w result : mul_small_input_bounds w ->
  radix_value result=literal_invert_numeric (fe_inv_value (swu_joint_words w)) ->
  radix_value result=modInv ((radix_value w+8)*(-3*radix_value w)) feP.
Proof.
  intros Bounds Value;rewrite Value,literal_invert_numeric_modInv by
    (apply (proj2 (fe_inv_value_range _))).
  apply modInv_eqm;unfold eqm,fe_inv_value.
  rewrite Z.mod_mod by (unfold feP,feR;lia);apply swu_joint_words_value;exact Bounds.
Qed.

Lemma exec_swu_joint_product_call e le m mf bj bw bx :
  e!_secp256k1_fe_mul=None -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x3d=Some (bx,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bj Ptrofs.zero;Vptr bw Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_joint_product E0 le mf Out_normal.
Proof.
  intros Fun J W X Call;unfold swu_joint_product;eapply exec_curve_call with
    (vargs:=[Vptr bj Ptrofs.zero;Vptr bw Ptrofs.zero;Vptr bx Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact J|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact W|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact X|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_joint_invert_call e le m mf bj :
  e!_secp256k1_fe_inv_var=None -> e!_jinv=Some (bj,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_inv_var)
    [Vptr bj Ptrofs.zero;Vptr bj Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_joint_invert E0 le mf Out_normal.
Proof.
  intros Fun J Call;unfold swu_joint_invert;eapply exec_curve_call with
    (vargs:=[Vptr bj Ptrofs.zero;Vptr bj Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact J|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact J|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_joint_inverse_compose e le m ms mp mf bj bw bx :
  e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_inv_var=None ->
  e!_jinv=Some (bj,curve_fe_type) -> e!_wd=Some (bw,curve_fe_type) -> e!_x3d=Some (bx,curve_fe_type) ->
  Clight2.exec_stmt secp_ge e le m swu_joint_setup E0 le ms Out_normal ->
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_fe_mul)
    [Vptr bj Ptrofs.zero;Vptr bw Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mp Vundef ->
  Clight2.eval_funcall secp_ge mp (Internal f_secp256k1_fe_inv_var)
    [Vptr bj Ptrofs.zero;Vptr bj Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_joint_inverse_prefix E0 le mf Out_normal.
Proof.
  intros EM EI EJ EW EX Setup Product Inverse.
  unfold swu_joint_inverse_prefix,swu_joint_inverse_statements.
  change (Clight2.exec_stmt secp_ge e le m (statement_sequence swu_joint_setup_statements
    (Ssequence swu_joint_product (Ssequence swu_joint_invert Sskip))) E0 le mf Out_normal).
  eapply exec_statement_prefix_then_last;[exact Setup|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mp);
    [eapply exec_swu_joint_product_call;eassumption|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);
    [eapply exec_swu_joint_invert_call;eassumption|apply exec_Sskip].
Qed.

Theorem exec_swu_joint_inverse e le m bw bx bj w :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_inv_var=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x3d=Some (bx,curve_fe_type) ->
  e!_jinv=Some (bj,curve_fe_type) -> NoDup [bw;bx;bj] -> swu_startup m ->
  mul_small_input_bounds w -> fe_at m bw 0 (words5 w) ->
  Mem.range_perm m bw 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  Mem.range_perm m bj 0 40 Cur Freeable -> exists result mf,
  Clight2.exec_stmt secp_ge e le m swu_joint_inverse_prefix E0 le mf Out_normal /\
  fe_at mf bw 0 (words5 (swu_setup_wd w)) /\ fe_at mf bx 0 (words5 (swu_setup_x3d w)) /\
  fe_at mf bj 0 (words5 result) /\ Mem.range_perm mf bw 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bj 0 40 Cur Freeable /\
  square_input_bounds result /\
  radix_value result=modInv ((radix_value w+8)*(-3*radix_value w)) feP /\ swu_startup mf /\
  lframe (fun b _=>b<>bw /\ b<>bx /\ b<>bj) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain EM EN EA EP EI EW EX EJ Sep Ready Bounds W FW FX FJ.
  assert (Pairs:bw<>bx /\ bw<>bj /\ bx<>bj) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Pairs as [WX [WJ XJ]].
  destruct (exec_swu_joint_setup e le m bw bx w Plain EM EN EA EW EX WX Ready Bounds W FW FX)
    as (ms & Setup & WS & XS & FWS & FXS & WV & XV & WB & XB & ReadyS & FS & RS).
  assert (FJS:Mem.range_perm ms bj 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FJ|exact FS|];intros;split;congruence. }
  destruct (eval_field_product_owned (swu_setup_wd w) (swu_setup_x3d w) ms bj bw bx WB XB
    ltac:(congruence) ltac:(congruence) WX FJS WS FWS XS FXS)
    as (mp & Product & JP & WP & XP & FJP & FWP & FXP & PV & JB & FP).
  assert (RP:readonly_preserved ms mp) by
    (eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Product]).
  assert (ReadyP:swu_startup mp) by (apply (swu_startup_preserved ms mp ReadyS RP)).
  assert (JBound:square_input_bounds (swu_joint_words w)).
  { unfold swu_joint_words;intros i Index;pose proof (JB i Index);destruct (Nat.eqb i 4);lia. }
  destruct (eval_fe_inverse_var_slice (swu_joint_words w) mp bj 0 bj 0 40 Count JBound JP
    (proj2 ReadyP) ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia) ltac:(lia) FJP)
    as (result & mf & Inverse & JF & ResultBounds & Value & Literal & FJF & Modulus & FI & RI).
  assert (WF:fe_at mf bw 0 (words5 (swu_setup_wd w))).
  { eapply curve_keep_field_range;[reflexivity|exact WP|exact FI|];intros;left;exact WJ. }
  assert (XF:fe_at mf bx 0 (words5 (swu_setup_x3d w))).
  { eapply curve_keep_field_range;[reflexivity|exact XP|exact FI|];intros;left;exact XJ. }
  assert (FWF:Mem.range_perm mf bw 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FWP|exact FI|];intros;left;exact WJ. }
  assert (FXF:Mem.range_perm mf bx 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FXP|exact FI|];intros;left;exact XJ. }
  exists result,mf;split.
  - eapply exec_swu_joint_inverse_compose;eassumption.
  - split;[exact WF|];split;[exact XF|];split;[exact JF|];split;[exact FWF|];split;[exact FXF|];
      split;[exact FJF|];split;[exact ResultBounds|];split;
      [apply (swu_joint_inverse_value w result Bounds Value)|];split;
      [apply (swu_startup_preserved mp mf ReadyP RI)|];split.
    + eapply lframe_trans with (m2:=ms).
      * eapply lframe_implies;[exact FS|];intros b pos [NW [NX NJ]] _;split;assumption.
      * eapply lframe_trans with (m2:=mp).
        -- eapply lframe_implies;[exact FP|];intros b pos [NW [NX NJ]] _;repeat split;assumption.
        -- eapply lframe_implies;[exact FI|];intros b pos [_ [_ NJ]] _;left;exact NJ.
    + eapply preserved_trans;[exact RS|];eapply preserved_trans;[exact RP|exact RI].
Qed.

Lemma swu_joint_inverse_congruent w t result : eqm feP (radix_value w) (t*t) ->
  radix_value result=modInv ((radix_value w+8)*(-3*radix_value w)) feP ->
  radix_value result=swu_joint_inverse t.
Proof.
  intros Input Value;rewrite Value;unfold swu_joint_inverse,swu_inv;apply modInv_eqm.
  replace (-3*t*t) with (-3*(t*t)) by ring;apply Zmult_eqm.
  - apply Zplus_eqm;[exact Input|reflexivity].
  - apply Zmult_eqm;[reflexivity|exact Input].
Qed.

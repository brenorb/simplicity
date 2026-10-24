(** Original first-candidate computation following the joint inversion.
    Both multiplications are the original in-place C calls, and d remains
    an initialized readonly global. No call execution or candidate value is
    assumed by the storage theorem. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_constant_product C.jet_secp_swu_constant_add C.jet_secp_swu_initial
  C.jet_secp_swu_joint_setup C.jet_secp_swu_joint_inverse C.jet_secp_swu_before_candidates
  C.jet_secp_field_pair_multiply C.jet_secp_field_add_scaled C.jet_secp_field_sum_bounds
  C.jet_secp_field_mul_small C.jet_secp_field_negate_magnitude C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_fns C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge swu_constant_block swu_constant_digits.

Definition swu_first_multiply (inv:bool) :=
  curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
    [curve_local_address _x1;curve_local_address _x1;
     curve_local_address (if inv then _jinv else _x3d)].
Definition swu_first_add_d := curve_call _secp256k1_fe_add f_secp256k1_fe_add None
  [curve_local_address _x1;curve_local_address _d].
Definition swu_first_statements :=
  [swu_first_multiply false;swu_first_multiply true;swu_first_add_d].
Definition swu_first_prefix := statement_sequence swu_first_statements Sskip.
Definition swu_after_first_candidate := match swu_after_joint_inverse with
  | Ssequence _ (Ssequence _ (Ssequence _ rest))=>rest | _=>Sskip end.
Lemma swu_first_source : swu_after_joint_inverse=
  statement_sequence swu_first_statements swu_after_first_candidate.
Proof. reflexivity. Qed.
Lemma exec_swu_first_multiply_call (inv:bool) e le m mf ba br :
  e!_secp256k1_fe_mul=None -> e!_x1=Some (ba,curve_fe_type) ->
  e!(if inv then _jinv else _x3d)=Some (br,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (swu_first_multiply inv) E0 le mf Out_normal.
Proof.
  intros Fun A R Call;unfold swu_first_multiply;eapply exec_curve_call with
    (vargs:=[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact A|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact A|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_first_add_call e le m mf ba :
  e!_secp256k1_fe_add=None -> e!_x1=Some (ba,curve_fe_type) -> e!_d=None ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr (swu_constant_block true) Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_first_add_d E0 le mf Out_normal.
Proof.
  intros Fun A D Call;unfold swu_first_add_d;eapply exec_curve_call with
    (vargs:=[Vptr ba Ptrofs.zero;Vptr (swu_constant_block true) Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact A|reflexivity|].
    eapply eval_Econs;[apply (eval_swu_constant_address true);exact D|reflexivity|constructor].
  - exact Call.
Qed.

Definition swu_first_product a xd inv := field_pair_product (field_pair_product a xd) inv.
Definition swu_first_words a xd inv :=
  field_sum_words (swu_first_product a xd inv) (swu_constant_digits true).
Theorem exec_swu_first_candidate e le m ba bx bj a xd inv :
  e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add=None -> e!_d=None ->
  e!_x1=Some (ba,curve_fe_type) -> e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  NoDup [ba;bx;bj] -> swu_startup m ->
  square_input_bounds a -> square_input_bounds xd -> square_input_bounds inv ->
  fe_at m ba 0 (words5 a) -> fe_at m bx 0 (words5 xd) -> fe_at m bj 0 (words5 inv) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  Mem.range_perm m bj 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_first_prefix E0 le mf Out_normal /\
  fe_at mf ba 0 (words5 (swu_first_words a xd inv)) /\
  fe_at mf bx 0 (words5 xd) /\ fe_at mf bj 0 (words5 inv) /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  Mem.range_perm mf bj 0 40 Cur Freeable /\ field_scaled_bounds 2 (swu_first_words a xd inv) /\
  square_input_bounds (swu_first_words a xd inv) /\
  eqm feP (radix_value (swu_first_words a xd inv))
    (radix_value a*radix_value xd*radix_value inv+swu_d_constant) /\
  swu_startup mf /\ lframe (fun b _=>b<>ba /\ b<>bx /\ b<>bj) m mf /\ readonly_preserved m mf.
Proof.
  intros EM EA ED EX EG EJ Sep Ready BA BX BJ A X J FA FX FJ.
  assert (Pairs:ba<>bx /\ ba<>bj /\ bx<>bj) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Pairs as [AX [AJ XJ]].
  destruct (eval_field_pair_multiply a xd m ba bx BA BX AX A X FA FX)
    as (m1 & Mul1 & A1 & X1 & FA1 & FX1 & V1 & B1 & T1 & F1).
  assert (J1:fe_at m1 bj 0 (words5 inv)).
  { eapply curve_keep_field_range;[reflexivity|exact J|exact F1|];intros;split;congruence. }
  assert (FJ1:Mem.range_perm m1 bj 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FJ|exact F1|];intros;split;congruence. }
  destruct (eval_field_pair_multiply (field_pair_product a xd) inv m1 ba bj B1 BJ AJ A1 J1 FA1 FJ1)
    as (m2 & Mul2 & A2 & J2 & FA2 & FJ2 & V2 & B2 & T2 & F2).
  assert (X2:fe_at m2 bx 0 (words5 xd)).
  { eapply curve_keep_field_range;[reflexivity|exact X1|exact F2|];intros;split;congruence. }
  assert (FX2:Mem.range_perm m2 bx 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FX1|exact F2|];intros;split;congruence. }
  assert (R1:readonly_preserved m m1) by
    (eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Mul1]).
  assert (R2:readonly_preserved m1 m2) by
    (eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Mul2]).
  assert (Ready2:swu_startup m2) by
    (eapply swu_startup_preserved;[exact Ready|eapply preserved_trans;eassumption]).
  assert (Tight2:mul_small_input_bounds (swu_first_product a xd inv)).
  { unfold swu_first_product;intros i Index;exact (proj2 (T2 i Index)). }
  destruct (eval_swu_constant_add true (swu_first_product a xd inv) m2 ba Ready2 Tight2 A2 FA2)
    as (mf & Add & AF & FAF & AddValue & Scaled & OutBounds & ReadyF & F3 & R3).
  assert (XF:fe_at mf bx 0 (words5 xd)).
  { eapply curve_keep_field_range;[reflexivity|exact X2|exact F3|];intros;congruence. }
  assert (JF:fe_at mf bj 0 (words5 inv)).
  { eapply curve_keep_field_range;[reflexivity|exact J2|exact F3|];intros;congruence. }
  assert (FXF:Mem.range_perm mf bx 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FX2|exact F3|];intros;congruence. }
  assert (FJF:Mem.range_perm mf bj 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FJ2|exact F3|];intros;congruence. }
  rewrite field_prime_matches_normalizer in V1,V2.
  assert (Value:eqm feP (radix_value (swu_first_words a xd inv))
    (radix_value a*radix_value xd*radix_value inv+swu_d_constant)).
  { unfold swu_first_words;rewrite AddValue;apply Zplus_eqm;[|reflexivity].
    eapply eqm_trans;[exact V2|];apply Zmult_eqm;[exact V1|reflexivity]. }
  exists mf;split.
  - unfold swu_first_prefix,swu_first_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);
      [eapply (exec_swu_first_multiply_call false);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m2);
      [eapply (exec_swu_first_multiply_call true);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);
      [eapply exec_swu_first_add_call;eassumption|apply exec_Sskip].
  - split;[exact AF|];split;[exact XF|];split;[exact JF|];split;[exact FAF|];split;[exact FXF|];
      split;[exact FJF|];split;[exact Scaled|];split;[exact OutBounds|];split;[exact Value|];
      split;[exact ReadyF|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact F1|];intros b pos [NW [NX NJ]] Valid;split;assumption.
      * eapply lframe_trans with (m2:=m2).
        -- eapply lframe_implies;[exact F2|];intros b pos [NW [NX NJ]] Valid;split;assumption.
        -- eapply lframe_implies;[exact F3|];intros b pos [NW Rest] Valid;exact NW.
    + eapply preserved_trans;[exact R1|];eapply preserved_trans;[exact R2|exact R3].
Qed.

Lemma swu_setup_x3d_square w : square_input_bounds w ->
  square_input_bounds (swu_setup_x3d (square_words w)) /\
  eqm feP (radix_value (swu_setup_x3d (square_words w))) (-3*radix_value w*radix_value w).
Proof.
  intro Bounds.
  assert (Tight:mul_small_input_bounds (square_words w)) by
    (intros i Index;exact (proj2 (square_output_bounds w Bounds i Index))).
  assert (C3:0<=Int.signed (Int.repr 3)<=7) by (change (0<=3<=7);lia).
  destruct (negate_mag_numeric (Int.repr 3) (mul_small_words (Int.repr 3) (square_words w)) C3
    (negate_mag_scaled_input (Int.repr 3) (square_words w) C3 Tight)) as [V B].
  split;[exact B|].
  unfold swu_setup_x3d;rewrite V,(mul_small_radix (Int.repr 3) (square_words w) C3 Tight).
  change (Int.signed (Int.repr 3)) with 3.
  replace (2*(3+1)*feP-3*radix_value (square_words w)) with
    (-3*radix_value (square_words w)+8*feP) by ring.
  unfold eqm;rewrite Z.mod_add by (unfold feP,feR;lia).
  replace (-3*radix_value w*radix_value w) with (-3*(radix_value w*radix_value w)) by ring.
  apply Zmult_eqm;[reflexivity|].
  pose proof (square_output_numeric w Bounds);rewrite field_prime_matches_normalizer in H;exact H.
Qed.
Lemma swu_first_spec_match t a xd inv value :
  eqm feP (radix_value a) (swu_negc_constant*t*t) ->
  eqm feP (radix_value xd) (-3*t*t) -> radix_value inv=swu_joint_inverse t ->
  eqm feP value (radix_value a*radix_value xd*radix_value inv+swu_d_constant) ->
  eqm feP value (swu_c_candidate1 t).
Proof.
  intros A X I V;eapply eqm_trans;[exact V|];rewrite I;unfold swu_c_candidate1.
  replace (swu_d_constant+swu_negc_constant*t*t*(-3*t*t)*swu_joint_inverse t) with
    ((swu_negc_constant*t*t)*(-3*t*t)*swu_joint_inverse t+swu_d_constant) by ring.
  apply Zplus_eqm;[|reflexivity].
  apply Zmult_eqm;[apply Zmult_eqm;assumption|reflexivity].
Qed.

Definition swu_through_first_statements := swu_before_candidates_statements++swu_first_statements.
Definition swu_through_first := statement_sequence swu_through_first_statements Sskip.
Lemma swu_through_first_source : fn_body f_shallue_van_de_woestijne=
  statement_sequence swu_through_first_statements swu_after_first_candidate.
Proof. reflexivity. Qed.
Theorem exec_swu_through_first e le m bt bw ba bx bj w :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  le!_t=Some (Vptr bt Ptrofs.zero) -> NoDup [bt;bw;ba;bx;bj] -> swu_startup m ->
  square_input_bounds w -> fe_at m bt 0 (words5 w) ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bt;bw;ba;bx;bj] -> exists inv mf,
  Clight2.exec_stmt secp_ge e le m swu_through_first E0 le mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\ fe_at mf bw 0 (words5 (swu_setup_wd (square_words w))) /\
  fe_at mf ba 0 (words5 (swu_first_words (swu_initial_a w) (swu_setup_x3d (square_words w)) inv)) /\
  fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w))) /\ fe_at mf bj 0 (words5 inv) /\
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bt;bw;ba;bx;bj] /\
  square_input_bounds inv /\
  field_scaled_bounds 2 (swu_first_words (swu_initial_a w) (swu_setup_x3d (square_words w)) inv) /\
  square_input_bounds (swu_first_words (swu_initial_a w) (swu_setup_x3d (square_words w)) inv) /\
  eqm feP (radix_value (swu_first_words (swu_initial_a w) (swu_setup_x3d (square_words w)) inv))
    (swu_c_candidate1 (radix_value w)) /\
  radix_value inv=swu_joint_inverse (radix_value w) /\ swu_startup mf /\
  lframe (fun b _=>~In b [bt;bw;ba;bx;bj]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED EW EX EXD EJ T Sep Ready Bounds Input Free.
  destruct (exec_swu_before_candidates e le m bt bw ba bx bj w Count Plain ES EM EN EC EG EA EI
    EW EX EXD EJ T Sep Ready Bounds Input Free)
    as (inv & ms & Start & TS & WS & AS & XS & JS & FreeS & JBounds & ABounds & ANumeric & JNumeric & ReadyS & FS & RS).
  assert (SepC:NoDup [ba;bx;bj]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  pose proof FreeS as AllFree;rewrite Forall_forall in AllFree.
  assert (FA:Mem.range_perm ms ba 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FX:Mem.range_perm ms bx 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FJ:Mem.range_perm ms bj 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (ABound:square_input_bounds (swu_initial_a w)).
  { intros i Index;pose proof (ABounds i Index);destruct (Nat.eqb i 4);lia. }
  destruct (swu_setup_x3d_square w Bounds) as [XBound XNumeric].
  destruct (exec_swu_first_candidate e le ms ba bx bj (swu_initial_a w)
    (swu_setup_x3d (square_words w)) inv EM EAdd ED EX EXD EJ SepC ReadyS ABound XBound
    JBounds AS XS JS FA FX FJ)
    as (mf & First & AF & XF & JF & FAF & FXF & FJF & Scaled & OutBounds & Value & ReadyF & FFirst & RFirst).
  assert (TF:fe_at mf bt 0 (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact TS|exact FFirst|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (WF:fe_at mf bw 0 (words5 (swu_setup_wd (square_words w)))).
  { eapply curve_keep_field_range;[reflexivity|exact WS|exact FFirst|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (FTF:Mem.range_perm mf bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia| |exact FFirst|];[apply AllFree;cbn;tauto|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (FWF:Mem.range_perm mf bw 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia| |exact FFirst|];[apply AllFree;cbn;tauto|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (Spec:eqm feP
    (radix_value (swu_first_words (swu_initial_a w) (swu_setup_x3d (square_words w)) inv))
    (swu_c_candidate1 (radix_value w))).
  { eapply swu_first_spec_match;[|exact XNumeric|exact JNumeric|exact Value].
    replace (swu_negc_constant*radix_value w*radix_value w) with
      (swu_negc_constant*(radix_value w*radix_value w)) by ring;exact ANumeric. }
  exists inv,mf;split.
  - unfold swu_through_first,swu_through_first_statements.
    change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence swu_before_candidates_statements swu_first_prefix) E0 le mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Start|exact First].
  - split;[exact TF|];split;[exact WF|];split;[exact AF|];split;[exact XF|];split;[exact JF|];split.
    + repeat constructor;assumption.
    + split;[exact JBounds|];split;[exact Scaled|];split;[exact OutBounds|];split;[exact Spec|];
        split;[exact JNumeric|];split;[exact ReadyF|];split.
      * eapply lframe_trans with (m2:=ms);[exact FS|].
        eapply lframe_implies;[exact FFirst|].
        intros b pos NotIn Valid;repeat split;intro Same;apply NotIn;subst;cbn;tauto.
      * eapply preserved_trans;[exact RS|exact RFirst].
Qed.

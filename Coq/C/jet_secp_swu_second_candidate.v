(** Original copy/add-one/magnitude-three negation for the second SWU
    candidate. Subtraction and no-wrap bounds follow from the first
    candidate's proved magnitude-two bounds. No normalization is inserted. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep
  Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_initial C.jet_secp_swu_joint_setup C.jet_secp_swu_before_candidates
  C.jet_secp_swu_first_candidate C.jet_secp_field_copy_owned
  C.jet_secp_field_add_int C.jet_secp_field_mul_small C.jet_secp_field_sum_bounds
  C.jet_secp_field_negate_magnitude C.jet_secp_field_negate_values
  C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_fns C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_second_copy := Sassign (Evar _x2 curve_fe_type) (Evar _x1 curve_fe_type).
Definition swu_second_add := curve_call _secp256k1_fe_add_int f_secp256k1_fe_add_int None
  [curve_local_address _x2;Econst_int (Int.repr 1) tint].
Definition swu_second_negate := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
  [curve_local_address _x2;curve_local_address _x2;Econst_int (Int.repr 3) tint].
Definition swu_second_statements := [swu_second_copy;swu_second_add;swu_second_negate].
Definition swu_second_prefix := statement_sequence swu_second_statements Sskip.
Definition swu_after_second_candidate := match swu_after_first_candidate with
  | Ssequence _ (Ssequence _ (Ssequence _ rest))=>rest | _=>Sskip end.
Definition swu_second_words a := negate_mag_words (Int.repr 3) (add_int_words (Int.repr 1) a).
Lemma swu_second_source : swu_after_first_candidate=
  statement_sequence swu_second_statements swu_after_second_candidate.
Proof. reflexivity. Qed.
Lemma swu_second_closed : closed_stmtb secp_closed_helpers swu_second_prefix=true.
Proof. vm_compute;reflexivity. Qed.

Lemma swu_second_add_bound a : field_scaled_bounds 2 a ->
  negate_mag_input_bounds (Int.repr 3) (add_int_words (Int.repr 1) a) /\
  radix_value (add_int_words (Int.repr 1) a)=radix_value a+1.
Proof.
  intro Bounds.
  assert (NoWrap:0<=Int64.unsigned (a 0%nat)+Int.signed (Int.repr 1)<=Int64.max_unsigned).
  { pose proof (Bounds 0%nat ltac:(lia)) as Low;cbn [Nat.eqb] in Low.
    pose proof (Int64.unsigned_range_2 (a 0%nat));change (Int.signed (Int.repr 1)) with 1;
      change Int64.max_unsigned with 18446744073709551615;lia. }
  split;[|exact (add_int_radix (Int.repr 1) a NoWrap)].
  intros i Index;change (Int.signed (Int.repr 3)) with 3.
  destruct (Nat.eqb i 0) eqn:Zero.
  - apply Nat.eqb_eq in Zero;subst i;rewrite add_int_unsigned_zero by exact NoWrap.
    change (Int.signed (Int.repr 1)) with 1;cbn [negate_mask].
    pose proof (Bounds 0%nat ltac:(lia));cbn [Nat.eqb] in H;lia.
  - unfold add_int_words;rewrite Zero;pose proof (Bounds i Index).
    destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask] in *;lia.
Qed.
Lemma exec_swu_second_add_call e le m mf b :
  e!_secp256k1_fe_add_int=None -> e!_x2=Some (b,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr b Ptrofs.zero;Vint (Int.repr 1)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_second_add E0 le mf Out_normal.
Proof.
  intros Fun B Call;unfold swu_second_add;eapply exec_curve_call with
    (vargs:=[Vptr b Ptrofs.zero;Vint (Int.repr 1)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact B|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_second_negate_call e le m mf b :
  e!_secp256k1_fe_negate=None -> e!_x2=Some (b,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero;Vint (Int.repr 3)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_second_negate E0 le mf Out_normal.
Proof.
  intros Fun B Call;unfold swu_second_negate;eapply exec_curve_call with
    (vargs:=[Vptr b Ptrofs.zero;Vptr b Ptrofs.zero;Vint (Int.repr 3)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact B|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact B|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.

Theorem exec_swu_second_candidate e le m ba bb a : plain_env e ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_negate=None ->
  e!_x1=Some (ba,curve_fe_type) -> e!_x2=Some (bb,curve_fe_type) -> ba<>bb ->
  swu_startup m -> field_scaled_bounds 2 a -> fe_at m ba 0 (words5 a) ->
  Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_second_prefix E0 le mf Out_normal /\
  fe_at mf ba 0 (words5 a) /\ fe_at mf bb 0 (words5 (swu_second_words a)) /\
  Mem.range_perm mf bb 0 40 Cur Freeable /\
  radix_value (swu_second_words a)=8*feP-(radix_value a+1) /\
  square_input_bounds (swu_second_words a) /\ swu_startup mf /\
  lframe (fun b _=>b<>bb) m mf /\ readonly_preserved m mf.
Proof.
  intros Plain EA EN AX BX Ne Ready Bounds Input Free.
  destruct (exec_field_copy_owned e le m (Evar _x1 curve_fe_type) (Evar _x2 curve_fe_type)
    ba 0 bb 0 a eq_refl eq_refl) as (mc & Copy & BC & Perms & FC).
  - eapply eval_Elvalue;[apply eval_Evar_local;exact AX|apply deref_loc_copy;reflexivity].
  - apply eval_Evar_local;exact BX.
  - exact Ne.
  - exact Input.
  - lia.
  - exists 0;reflexivity.
  - change (40<=18446744073709551615);lia.
  - exact Free.
  - assert (FBC:Mem.range_perm mc bb 0 40 Cur Freeable) by
      (intros pos Range;apply Perms;apply Free;exact Range).
    destruct (eval_field_add_int_from_storage (Int.repr 1) a mc bb BC FBC)
      as (mp & Add & BP & FBP & FP).
    destruct (swu_second_add_bound a Bounds) as [NegBound PlusValue].
    destruct (eval_negate_mag_bounded (Int.repr 3) (add_int_words (Int.repr 1) a) mp bb
      ltac:(change (0<=3<=7);lia) NegBound BP FBP)
      as (mf & Neg & BF & FBF & NegValue & OutBounds & FN).
    assert (Frame:lframe (fun b _=>b<>bb) m mf).
    { eapply lframe_trans with (m2:=mc).
      - eapply lframe_implies;[exact FC|];intros b pos NeB Valid;left;exact NeB.
      - eapply lframe_trans;[exact FP|exact FN]. }
    assert (AF:fe_at mf ba 0 (words5 a)) by
      (eapply curve_keep_field_range;[reflexivity|exact Input|exact Frame|];intros;exact Ne).
    assert (Run:Clight2.exec_stmt secp_ge e le m swu_second_prefix E0 le mf Out_normal).
    { unfold swu_second_prefix,swu_second_statements;cbn [statement_sequence].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mc);[exact Copy|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mp);
        [eapply exec_swu_second_add_call;eassumption|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);
        [eapply exec_swu_second_negate_call;eassumption|apply exec_Sskip]. }
    assert (Readonly:readonly_preserved m mf) by
      (eapply secp_closed_stmt_preserved;[exact Run|exact Plain|exact swu_second_closed]).
    change (radix_value (swu_second_words a)=8*feP-radix_value (add_int_words (Int.repr 1) a)) in NegValue.
    rewrite PlusValue in NegValue.
    exists mf;split;[exact Run|];split;[exact AF|];split;[exact BF|];split;[exact FBF|];
      split;[exact NegValue|];split;[exact OutBounds|];split;
      [apply (swu_startup_preserved m mf Ready Readonly)|];split;assumption.
Qed.

Lemma swu_second_spec_match a t value : eqm feP (radix_value a) (swu_c_candidate1 t) ->
  value=8*feP-(radix_value a+1) -> eqm feP value (swu_c_candidate2 t).
Proof.
  intros First Value;rewrite Value;unfold swu_c_candidate2.
  replace (8*feP-(radix_value a+1)) with (-(radix_value a+1)+8*feP) by ring.
  unfold eqm;rewrite Z.mod_add by (unfold feP,feR;lia).
  apply Zopp_eqm;apply Zplus_eqm;[exact First|reflexivity].
Qed.
Definition swu_input_first_words w inv :=
  swu_first_words (swu_initial_a w) (swu_setup_x3d (square_words w)) inv.
Definition swu_through_second_statements := swu_through_first_statements++swu_second_statements.
Definition swu_through_second := statement_sequence swu_through_second_statements Sskip.
Lemma swu_through_second_source : fn_body f_shallue_van_de_woestijne=
  statement_sequence swu_through_second_statements swu_after_second_candidate.
Proof. reflexivity. Qed.

Theorem exec_swu_through_second e le m bt bw ba bx bj bb w :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_x2=Some (bb,curve_fe_type) -> le!_t=Some (Vptr bt Ptrofs.zero) ->
  NoDup [bt;bw;ba;bx;bj;bb] -> swu_startup m -> square_input_bounds w -> fe_at m bt 0 (words5 w) ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb] -> exists inv mf,
  Clight2.exec_stmt secp_ge e le m swu_through_second E0 le mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\ fe_at mf bw 0 (words5 (swu_setup_wd (square_words w))) /\
  fe_at mf ba 0 (words5 (swu_input_first_words w inv)) /\
  fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w))) /\ fe_at mf bj 0 (words5 inv) /\
  fe_at mf bb 0 (words5 (swu_second_words (swu_input_first_words w inv))) /\
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb] /\
  square_input_bounds inv /\ field_scaled_bounds 2 (swu_input_first_words w inv) /\
  square_input_bounds (swu_input_first_words w inv) /\
  square_input_bounds (swu_second_words (swu_input_first_words w inv)) /\
  eqm feP (radix_value (swu_input_first_words w inv)) (swu_c_candidate1 (radix_value w)) /\
  eqm feP (radix_value (swu_second_words (swu_input_first_words w inv))) (swu_c_candidate2 (radix_value w)) /\
  radix_value inv=swu_joint_inverse (radix_value w) /\ swu_startup mf /\
  lframe (fun b _=>~In b [bt;bw;ba;bx;bj;bb]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED EW EX EXD EJ EX2 T Sep Ready Bounds Input Free.
  assert (SepF:NoDup [bt;bw;ba;bx;bj]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  assert (FreeF:Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bt;bw;ba;bx;bj]).
  { rewrite Forall_forall in *;intros b Member;apply Free;cbn [In] in *;tauto. }
  destruct (exec_swu_through_first e le m bt bw ba bx bj w Count Plain ES EM EN EC EG EA EI
    EAdd ED EW EX EXD EJ T SepF Ready Bounds Input FreeF)
    as (inv & ms & Start & TS & WS & AS & XS & JS & FreeS & JBounds & Scaled & ABounds & FirstSpec & JNumeric & ReadyS & FS & RS).
  assert (NotBB:~In bb [bt;bw;ba;bx;bj]) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
  assert (FBB:Mem.range_perm m bb 0 40 Cur Freeable).
  { rewrite Forall_forall in Free;apply Free;cbn;tauto. }
  assert (FBBS:Mem.range_perm ms bb 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FBB|exact FS|];intros;exact NotBB).
  assert (AB:ba<>bb) by (intro Same;apply NotBB;subst;cbn;tauto).
  destruct (exec_swu_second_candidate e le ms ba bb (swu_input_first_words w inv) Plain EA EG
    EX EX2 AB ReadyS Scaled AS FBBS)
    as (mf & Second & AF & BF & FBBF & Value2 & BBounds & ReadyF & FSecond & RSecond).
  assert (TF:fe_at mf bt 0 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact TS|exact FSecond|];
     intros;intro Same;apply NotBB;subst;cbn;tauto).
  assert (WF:fe_at mf bw 0 (words5 (swu_setup_wd (square_words w)))) by
    (eapply curve_keep_field_range;[reflexivity|exact WS|exact FSecond|];
     intros;intro Same;apply NotBB;subst;cbn;tauto).
  assert (XF:fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w)))) by
    (eapply curve_keep_field_range;[reflexivity|exact XS|exact FSecond|];
     intros;intro Same;apply NotBB;subst;cbn;tauto).
  assert (JF:fe_at mf bj 0 (words5 inv)) by
    (eapply curve_keep_field_range;[reflexivity|exact JS|exact FSecond|];
     intros;intro Same;apply NotBB;subst;cbn;tauto).
  assert (FreeFinal:Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb]).
  { change (Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) ([bt;bw;ba;bx;bj]++[bb])).
    apply Forall_app;split.
    - rewrite Forall_forall in FreeS|-*;intros b Old.
      eapply curve_keep_free;[lia|apply FreeS;exact Old|exact FSecond|];
        intros;intro Same;apply NotBB;subst;exact Old.
    - constructor;[exact FBBF|constructor]. }
  assert (Spec2:eqm feP (radix_value (swu_second_words (swu_input_first_words w inv)))
    (swu_c_candidate2 (radix_value w))) by
    (eapply swu_second_spec_match;[exact FirstSpec|exact Value2]).
  exists inv,mf;split.
  - unfold swu_through_second,swu_through_second_statements.
    change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence swu_through_first_statements swu_second_prefix) E0 le mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Start|exact Second].
  - split;[exact TF|];split;[exact WF|];split;[exact AF|];split;[exact XF|];split;[exact JF|];
      split;[exact BF|];split;[exact FreeFinal|];split;[exact JBounds|];split;[exact Scaled|];
      split;[exact ABounds|];split;[exact BBounds|];split;[exact FirstSpec|];split;[exact Spec2|];
      split;[exact JNumeric|];split;[exact ReadyF|];split.
    + eapply lframe_trans with (m2:=ms).
      * eapply lframe_implies;[exact FS|];intros b pos NotIn Valid;cbn [In] in *;tauto.
      * eapply lframe_implies;[exact FSecond|];
          intros b pos NotIn Valid;intro Same;apply NotIn;subst;cbn;tauto.
    + eapply preserved_trans;[exact RS|exact RSecond].
Qed.

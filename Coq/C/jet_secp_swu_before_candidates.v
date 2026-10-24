(** Original first eight SWU statements, composed from input storage.
    The square and joint-denominator representations are derived, not assumed.
    CTZ remains the explicit original-call premise inherited from fe_inv_var. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_initial C.jet_secp_swu_joint_setup C.jet_secp_swu_joint_inverse
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_field_mul_small
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_before_candidates_statements :=
  [swu_initial_square;swu_initial_product]++swu_joint_inverse_statements.
Definition swu_before_candidates := statement_sequence swu_before_candidates_statements Sskip.
Lemma swu_before_candidates_source : fn_body f_shallue_van_de_woestijne=
  statement_sequence swu_before_candidates_statements swu_after_joint_inverse.
Proof. reflexivity. Qed.
Lemma exec_swu_initial_then e le m lm mm lf mf suffix out :
  Clight2.exec_stmt secp_ge e le m (Ssequence swu_initial_square swu_initial_product)
    E0 lm mm Out_normal ->
  Clight2.exec_stmt secp_ge e lm mm suffix E0 lf mf out ->
  Clight2.exec_stmt secp_ge e le m
    (Ssequence swu_initial_square (Ssequence swu_initial_product suffix)) E0 lf mf out.
Proof.
  intros Start Tail;inversion Start;subst.
  - match goal with H:?t1 ** ?t2=E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
    change E0 with (E0 ** E0);eapply exec_Sseq_1;[eassumption|].
    change E0 with (E0 ** E0);eapply exec_Sseq_1;eassumption.
  - contradiction.
Qed.

Theorem exec_swu_before_candidates e le m bt bw ba bx bj w :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  le!_t=Some (Vptr bt Ptrofs.zero) -> NoDup [bt;bw;ba;bx;bj] -> swu_startup m ->
  square_input_bounds w -> fe_at m bt 0 (words5 w) ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bt;bw;ba;bx;bj] -> exists result mf,
  Clight2.exec_stmt secp_ge e le m swu_before_candidates E0 le mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\ fe_at mf bw 0 (words5 (swu_setup_wd (square_words w))) /\
  fe_at mf ba 0 (words5 (swu_initial_a w)) /\
  fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w))) /\ fe_at mf bj 0 (words5 result) /\
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bt;bw;ba;bx;bj] /\
  square_input_bounds result /\ mul_small_input_bounds (swu_initial_a w) /\
  radix_value (swu_initial_a w) mod feP=(swu_negc_constant*(radix_value w*radix_value w)) mod feP /\
  radix_value result=swu_joint_inverse (radix_value w) /\ swu_startup mf /\
  lframe (fun b _=>~In b [bt;bw;ba;bx;bj]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EW EX ED EJ T Sep Ready Bounds Input Free.
  pose proof Free as AllFree;rewrite Forall_forall in AllFree.
  assert (FT:Mem.range_perm m bt 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FW:Mem.range_perm m bw 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FA:Mem.range_perm m ba 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FX:Mem.range_perm m bx 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FJ:Mem.range_perm m bj 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (SepI:NoDup [bt;bw;ba]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  assert (SepJ:NoDup [bw;bx;bj]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  destruct (exec_swu_initial e le m bt bw ba w ES EM EN EW EX T SepI Ready Bounds Input FT FW FA)
    as (ms & Start & TS & WS & AS & FTS & FWS & FAS & ANumeric & ABounds & ReadyS & FS & RS).
  assert (FXS:Mem.range_perm ms bx 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FX|exact FS|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (FJS:Mem.range_perm ms bj 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FJ|exact FS|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (SquareTight:mul_small_input_bounds (square_words w)).
  { intros i Index;exact (proj2 (square_output_bounds w Bounds i Index)). }
  destruct (exec_swu_joint_inverse e le ms bw bx bj (square_words w) Count Plain EC EG EA EM EI
    EW ED EJ SepJ ReadyS SquareTight WS FWS FXS FJS)
    as (result & mf & Joint & WF & XF & JF & FWF & FXF & FJF & JBounds & JNumeric & ReadyF & FJoint & RJoint).
  assert (TF:fe_at mf bt 0 (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact TS|exact FJoint|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (AF:fe_at mf ba 0 (words5 (swu_initial_a w))).
  { eapply curve_keep_field_range;[reflexivity|exact AS|exact FJoint|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (FTF:Mem.range_perm mf bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FTS|exact FJoint|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (FAF:Mem.range_perm mf ba 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FAS|exact FJoint|];intros;repeat split;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  assert (InvValue:radix_value result=swu_joint_inverse (radix_value w)).
  { pose proof (square_output_numeric w Bounds) as Square;rewrite field_prime_matches_normalizer in Square.
    exact (swu_joint_inverse_congruent (square_words w) (radix_value w) result Square JNumeric). }
  exists result,mf;split.
  - unfold swu_before_candidates,swu_before_candidates_statements;cbn [app statement_sequence].
    eapply exec_swu_initial_then;[exact Start|exact Joint].
  - split;[exact TF|];split;[exact WF|];split;[exact AF|];split;[exact XF|];split;[exact JF|];split.
    + repeat constructor;assumption.
    + split;[exact JBounds|];split;[exact ABounds|];split;[exact ANumeric|];split;
        [exact InvValue|];split;[exact ReadyF|];split.
      * eapply lframe_trans with (m2:=ms).
        -- eapply (lframe_implies _ _ m ms FS).
           intros b pos NotIn Valid;repeat split;intro Same;apply NotIn;subst;cbn;tauto.
        -- eapply (lframe_implies _ _ ms mf FJoint).
           intros b pos NotIn Valid;repeat split;intro Same;apply NotIn;subst;cbn;tauto.
      * eapply preserved_trans;[exact RS|exact RJoint].
Qed.

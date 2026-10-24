(** Compose every original statement before the SWU square-root calls.
    The three candidate and radicand representations are derived from the
    input and uninitialized owned locals, with the original CTZ contract
    still explicit. This is a prefix, not a public-jet registration. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_initial C.jet_secp_swu_joint_setup C.jet_secp_swu_first_candidate
  C.jet_secp_swu_second_candidate C.jet_secp_swu_third_candidate C.jet_secp_swu_cubics
  C.jet_secp_field_sum_bounds C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_statement_prefix C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_through_cubics_statements := swu_through_third_statements++swu_cubics_statements.
Definition swu_through_cubics := statement_sequence swu_through_cubics_statements Sskip.
Lemma swu_through_cubics_source : fn_body f_shallue_van_de_woestijne=
  statement_sequence swu_through_cubics_statements swu_after_cubics.
Proof. reflexivity. Qed.

Theorem exec_swu_through_cubics e le m bt bw ba bx bj bb bc bA bB bC w :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_x2=Some (bb,curve_fe_type) -> e!_x3=Some (bc,curve_fe_type) ->
  e!_alphain=Some (bA,curve_fe_type) -> e!_betain=Some (bB,curve_fe_type) ->
  e!_gammain=Some (bC,curve_fe_type) -> le!_t=Some (Vptr bt Ptrofs.zero) ->
  NoDup [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC] ->
  swu_startup m -> square_input_bounds w -> fe_at m bt 0 (words5 w) ->
  Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC] -> exists inv mf,
  Clight2.exec_stmt secp_ge e le m swu_through_cubics E0 le mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\ fe_at mf bw 0 (words5 (swu_setup_wd (square_words w))) /\
  fe_at mf ba 0 (words5 (swu_input_first_words w inv)) /\
  fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w))) /\ fe_at mf bj 0 (words5 inv) /\
  fe_at mf bb 0 (words5 (swu_second_words (swu_input_first_words w inv))) /\
  fe_at mf bc 0 (words5 (swu_input_third_words w inv)) /\
  fe_at mf bA 0 (words5 (swu_cubic_words (swu_input_first_words w inv))) /\
  fe_at mf bB 0 (words5 (swu_cubic_words (swu_second_words (swu_input_first_words w inv)))) /\
  fe_at mf bC 0 (words5 (swu_cubic_words (swu_input_third_words w inv))) /\
  Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC] /\
  square_input_bounds inv /\ square_input_bounds (swu_input_first_words w inv) /\
  square_input_bounds (swu_second_words (swu_input_first_words w inv)) /\
  square_input_bounds (swu_input_third_words w inv) /\
  Forall (field_scaled_bounds 2)
    [swu_cubic_words (swu_input_first_words w inv);
     swu_cubic_words (swu_second_words (swu_input_first_words w inv));
     swu_cubic_words (swu_input_third_words w inv)] /\
  Forall square_input_bounds
    [swu_cubic_words (swu_input_first_words w inv);
     swu_cubic_words (swu_second_words (swu_input_first_words w inv));
     swu_cubic_words (swu_input_third_words w inv)] /\
  eqm feP (radix_value (swu_input_first_words w inv)) (swu_c_candidate1 (radix_value w)) /\
  eqm feP (radix_value (swu_second_words (swu_input_first_words w inv))) (swu_c_candidate2 (radix_value w)) /\
  eqm feP (radix_value (swu_input_third_words w inv)) (swu_c_candidate3 (radix_value w)) /\
  eqm feP (radix_value (swu_cubic_words (swu_input_first_words w inv)))
    (swu_cubic (swu_c_candidate1 (radix_value w))) /\
  eqm feP (radix_value (swu_cubic_words (swu_second_words (swu_input_first_words w inv))))
    (swu_cubic (swu_c_candidate2 (radix_value w))) /\
  eqm feP (radix_value (swu_cubic_words (swu_input_third_words w inv)))
    (swu_cubic (swu_c_candidate3 (radix_value w))) /\
  radix_value inv=swu_joint_inverse (radix_value w) /\ swu_startup mf /\
  lframe (fun bi _=>~In bi [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma
    T Sep Ready Bounds Input Free.
  assert (SepS:NoDup [bt;bw;ba;bx;bj;bb;bc]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  assert (FreeS0:Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc]).
  { rewrite Forall_forall in *;intros bi Member;apply Free;cbn [In] in *;tauto. }
  destruct (exec_swu_through_third e le m bt bw ba bx bj bb bc w Count Plain ES EM EN EC EG EA EI
    EAdd ED EW EX EXD EJ EX2 EX3 T SepS Ready Bounds Input FreeS0)
    as (inv & ms & Start & TS & WS & AS & XS & JS & BS & CS & FreeS & JBounds & AScaled &
      ABounds & BBounds & CScaled & CBounds & Spec1 & Spec2 & Spec3 & JNumeric & ReadyS & FS & RS).
  assert (NewOutside:forall bi,In bi [bA;bB;bC] -> ~In bi [bt;bw;ba;bx;bj;bb;bc]).
  { intros bi Member;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence. }
  assert (SepC:NoDup [ba;bb;bc;bA;bB;bC]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  pose proof Free as All0;rewrite Forall_forall in All0.
  pose proof FreeS as AllS;rewrite Forall_forall in AllS.
  assert (FreeC:Forall (fun bi=>Mem.range_perm ms bi 0 40 Cur Freeable) [ba;bb;bc;bA;bB;bC]).
  { change (Forall (fun bi=>Mem.range_perm ms bi 0 40 Cur Freeable) ([ba;bb;bc]++[bA;bB;bC])).
    apply Forall_app;split;rewrite Forall_forall;intros bi Member.
    - apply AllS;cbn [In] in *;tauto.
    - eapply curve_keep_free;[lia|apply All0;cbn [In] in *;tauto|exact FS|].
      intros;apply NewOutside;exact Member. }
  destruct (exec_swu_cubics e le ms ba bb bc bA bB bC (swu_input_first_words w inv)
    (swu_second_words (swu_input_first_words w inv)) (swu_input_third_words w inv)
    ES EM EA EX EX2 EX3 EAlpha EBeta EGamma SepC ABounds BBounds CBounds AS BS CS FreeC)
    as (mf & Cubics & AF & BF & CF & Alpha & Beta & Gamma & FreeCubics & SA & OA & SB & OB &
      SC & OC & VA & VB & VC & FC & RC).
  assert (Safe:forall bi,In bi [bt;bw;bx;bj] -> ~In bi [ba;bb;bc;bA;bB;bC]).
  { intros bi Member;clear -Sep Member;
      repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence. }
  assert (Keep:forall bi rho,In bi [bt;bw;bx;bj] ->
    fe_at ms bi 0 (words5 rho) -> fe_at mf bi 0 (words5 rho)).
  { intros bi rho Member Field;eapply curve_keep_field_range;
      [reflexivity|exact Field|exact FC|];intros;apply Safe;exact Member. }
  assert (TF:fe_at mf bt 0 (words5 w)) by (eapply Keep;[cbn;tauto|exact TS]).
  assert (WF:fe_at mf bw 0 (words5 (swu_setup_wd (square_words w)))) by
    (eapply Keep;[cbn;tauto|exact WS]).
  assert (XF:fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w)))) by
    (eapply Keep;[cbn;tauto|exact XS]).
  assert (JF:fe_at mf bj 0 (words5 inv)) by (eapply Keep;[cbn;tauto|exact JS]).
  assert (FreeFinal:Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable)
    [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC]).
  { rewrite Forall_forall in FreeCubics|-*;intros bi Member.
    destruct (in_dec Pos.eq_dec bi [ba;bb;bc;bA;bB;bC]) as [Touched|Outside].
    - apply FreeCubics;exact Touched.
    - eapply curve_keep_free;[lia| |exact FC|intros;exact Outside].
      apply AllS;clear -Member Outside;cbn [In] in *;tauto. }
  assert (SpecA:eqm feP (radix_value (swu_cubic_words (swu_input_first_words w inv)))
    (swu_cubic (swu_c_candidate1 (radix_value w)))) by
    (eapply swu_cubic_spec_match;[exact VA|exact Spec1]).
  assert (SpecB:eqm feP (radix_value (swu_cubic_words (swu_second_words (swu_input_first_words w inv))))
    (swu_cubic (swu_c_candidate2 (radix_value w)))) by
    (eapply swu_cubic_spec_match;[exact VB|exact Spec2]).
  assert (SpecC:eqm feP (radix_value (swu_cubic_words (swu_input_third_words w inv)))
    (swu_cubic (swu_c_candidate3 (radix_value w)))) by
    (eapply swu_cubic_spec_match;[exact VC|exact Spec3]).
  assert (ReadyF:swu_startup mf) by (eapply swu_startup_preserved;[exact ReadyS|exact RC]).
  exists inv,mf;split.
  - unfold swu_through_cubics,swu_through_cubics_statements.
    change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence swu_through_third_statements swu_cubics_prefix) E0 le mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Start|exact Cubics].
  - split;[exact TF|];split;[exact WF|];split;[exact AF|];split;[exact XF|];split;[exact JF|];
      split;[exact BF|];split;[exact CF|];split;[exact Alpha|];split;[exact Beta|];split;[exact Gamma|];
      split;[exact FreeFinal|];split;[exact JBounds|];split;[exact ABounds|];split;[exact BBounds|];
      split;[exact CBounds|];split;[repeat constructor;assumption|];
      split;[repeat constructor;assumption|];split;[exact Spec1|];split;[exact Spec2|];
      split;[exact Spec3|];split;[exact SpecA|];split;[exact SpecB|];split;[exact SpecC|];
      split;[exact JNumeric|];split;[exact ReadyF|];split.
    + eapply lframe_trans with (m2:=ms).
      * eapply lframe_implies;[exact FS|];intros bi pos Outside Valid;cbn [In] in *;tauto.
      * eapply lframe_implies;[exact FC|];intros bi pos Outside Valid;cbn [In] in *;tauto.
    + eapply preserved_trans;[exact RS|exact RC].
Qed.

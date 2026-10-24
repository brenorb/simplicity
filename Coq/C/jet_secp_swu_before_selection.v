(** Input-driven original SWU execution through all three square-root calls.
    Keeps the six candidate coordinates, their literal field relations,
    exact check flags, all caller-owned objects and the original suffix. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Values Events Maps.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.extraMath C.modinv C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_first_candidate C.jet_secp_swu_second_candidate C.jet_secp_swu_third_candidate
  C.jet_secp_swu_cubics C.jet_secp_swu_before_roots C.jet_secp_swu_root_inputs C.jet_secp_swu_roots
  C.jet_secp_swu_literal C.jet_secp_swu_literal_bridge C.jet_secp_root_chain_numeric
  C.jet_secp_root_check C.jet_secp_root_literal C.jet_secp_rescale_literal
  C.jet_secp_root_output_bounds C.jet_secp_field_mul_small
  C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_chain_candidate literal_swu_candidates literal_root_candidate
  literal_fe_add literal_fe_negate literal_fe_one256 rescale_field_output.

Definition swu_alpha_words w inv := swu_cubic_words (swu_input_first_words w inv).
Definition swu_beta_words w inv := swu_cubic_words (swu_second_words (swu_input_first_words w inv)).
Definition swu_gamma_words w inv := swu_cubic_words (swu_input_third_words w inv).
Definition swu_through_roots_statements := swu_through_cubics_statements++swu_roots_statements.
Definition swu_through_roots := statement_sequence swu_through_roots_statements Sskip.
Definition swu_selection_temps w inv le := swu_roots_temps (swu_alpha_words w inv) (swu_beta_words w inv) le.
Lemma swu_through_roots_source : fn_body f_shallue_van_de_woestijne=
  statement_sequence swu_through_roots_statements swu_after_roots.
Proof. reflexivity. Qed.

Lemma swu_nodup_app_apart (before after:list block) : NoDup (before++after) ->
  forall bi,In bi before -> ~In bi after.
Proof.
  induction before as [|head tail IH];cbn [app];intros Sep bi Member Other;[contradiction|].
  apply NoDup_cons_iff in Sep;destruct Sep as [NotHead Tail].
  destruct Member as [Same|Member].
  - subst bi;apply NotHead;apply in_or_app;right;exact Other.
  - exact (IH Tail bi Member Other).
Qed.

Lemma swu_candidate_fields_match (t:Ty.tySem (Word 8)) w a b c :
  root_words_match w t -> square_input_bounds a -> square_input_bounds b -> square_input_bounds c ->
  eqm feP (radix_value a) (swu_c_candidate1 (radix_value w)) ->
  eqm feP (radix_value b) (swu_c_candidate2 (radix_value w)) ->
  eqm feP (radix_value c) (swu_c_candidate3 (radix_value w)) ->
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  root_words_match a x1 /\ root_words_match b
    (@literal_fe_negate Alg.CoreFunSem (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt))) /\
  root_words_match c x3.
Proof.
  intros [BW Input] BA BB BC VA VB VC;pose proof (swu_literal_candidates_c t) as Spec.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [x1 x3];destruct Spec as [X1 X3].
  split;[|split];split;try assumption.
  - eapply eqm_trans;[exact VA|];eapply eqm_trans;[apply swu_candidate1_eqm;exact Input|].
    apply eqm_sym;exact X1.
  - eapply eqm_trans;[exact VB|];eapply eqm_trans;[apply swu_candidate2_eqm;exact Input|].
    apply eqm_sym;apply swu_second_candidate_match;exact X1.
  - eapply eqm_trans;[exact VC|];eapply eqm_trans;[apply swu_candidate3_eqm;exact Input|].
    apply eqm_sym;exact X3.
Qed.

Theorem exec_swu_through_roots e le m bt bw ba bx bj bb bc bA bB bC by1 by2 by3 w (t:Ty.tySem (Word 8)) :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None -> e!_secp256k1_fe_sqrt_var=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_x2=Some (bb,curve_fe_type) -> e!_x3=Some (bc,curve_fe_type) ->
  e!_alphain=Some (bA,curve_fe_type) -> e!_betain=Some (bB,curve_fe_type) ->
  e!_gammain=Some (bC,curve_fe_type) -> e!_y1=Some (by1,curve_fe_type) ->
  e!_y2=Some (by2,curve_fe_type) -> e!_y3=Some (by3,curve_fe_type) ->
  le!_t=Some (Vptr bt Ptrofs.zero) -> NoDup [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] ->
  swu_startup m -> root_words_match w t -> fe_at m bt 0 (words5 w) ->
  Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] ->
  exists inv mf,
  Clight2.exec_stmt secp_ge e le m swu_through_roots E0 (swu_selection_temps w inv le) mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\
  fe_at mf ba 0 (words5 (swu_input_first_words w inv)) /\
  fe_at mf bb 0 (words5 (swu_second_words (swu_input_first_words w inv))) /\
  fe_at mf bc 0 (words5 (swu_input_third_words w inv)) /\
  fe_at mf by1 0 (words5 (root_chain_candidate (swu_alpha_words w inv))) /\
  fe_at mf by2 0 (words5 (root_chain_candidate (swu_beta_words w inv))) /\
  fe_at mf by3 0 (words5 (root_chain_candidate (swu_gamma_words w inv))) /\
  Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] /\
  Forall square_input_bounds
    [swu_input_first_words w inv;swu_second_words (swu_input_first_words w inv);swu_input_third_words w inv;
     root_chain_candidate (swu_alpha_words w inv);root_chain_candidate (swu_beta_words w inv);
     root_chain_candidate (swu_gamma_words w inv)] /\
  Forall mul_small_input_bounds
    [root_chain_candidate (swu_alpha_words w inv);root_chain_candidate (swu_beta_words w inv);
     root_chain_candidate (swu_gamma_words w inv)] /\
  swu_startup mf /\
  lframe (fun bi _=>~In bi [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]) m mf /\ readonly_preserved m mf /\
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  let x2:=@literal_fe_negate Alg.CoreFunSem (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt)) in
  root_words_match (swu_input_first_words w inv) x1 /\
  root_words_match (swu_second_words (swu_input_first_words w inv)) x2 /\
  root_words_match (swu_input_third_words w inv) x3 /\
  rescale_field_output (root_chain_candidate (swu_alpha_words w inv))=literal_root_candidate (swu_radicand x1) /\
  rescale_field_output (root_chain_candidate (swu_beta_words w inv))=literal_root_candidate (swu_radicand x2) /\
  rescale_field_output (root_chain_candidate (swu_gamma_words w inv))=literal_root_candidate (swu_radicand x3) /\
  root_check_flag (swu_alpha_words w inv)=Bit.toBool (literal_root_check (swu_radicand x1)) /\
  root_check_flag (swu_beta_words w inv)=Bit.toBool (literal_root_check (swu_radicand x2)) /\
  root_check_flag (swu_gamma_words w inv)=Bit.toBool (literal_root_check (swu_radicand x3)).
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED ERoot EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma
    EY1 EY2 EY3 T Sep Ready Match Input Free.
  assert (SepS:NoDup [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC]) by
    (exact (@NoDup_app_remove_r block [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC] [by1;by2;by3] Sep)).
  assert (FreeS0:Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC]).
  { rewrite Forall_forall in *;intros bi Member;apply Free;clear -Member;cbn [In] in *;tauto. }
  destruct (exec_swu_through_cubics e le m bt bw ba bx bj bb bc bA bB bC w Count Plain
    ES EM EN EC EG EA EI EAdd ED EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma T SepS Ready
    (proj1 Match) Input FreeS0)
    as (inv & ms & Start & TS & WS & AS & XS & JS & BS & CS & Alpha & Beta & Gamma & FreeS &
      JBounds & ABounds & BBounds & CBounds & Scaled & RadBounds & Spec1 & Spec2 & Spec3 &
      SpecA & SpecB & SpecC & JNumeric & ReadyS & FS & RS).
  pose proof (swu_root_inputs_match t w (swu_alpha_words w inv) (swu_beta_words w inv)
    (swu_gamma_words w inv) Match) as RootMatches.
  assert (RBounds: square_input_bounds (swu_alpha_words w inv) /\
    square_input_bounds (swu_beta_words w inv) /\ square_input_bounds (swu_gamma_words w inv)).
  { inversion RadBounds as [|r rest RA Tail];inversion Tail as [|s ss RB Tail2];
      inversion Tail2 as [|u us RC Tail3];repeat split;assumption. }
  destruct RBounds as [RA [RB RC]].
  specialize (RootMatches RA RB RC SpecA SpecB SpecC).
  pose proof (swu_candidate_fields_match t w (swu_input_first_words w inv)
    (swu_second_words (swu_input_first_words w inv)) (swu_input_third_words w inv)
    Match ABounds BBounds CBounds Spec1 Spec2 Spec3) as CandidateMatches.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [x1 x3].
  destruct RootMatches as [MA [MB MC]];destruct CandidateMatches as [MX1 [MX2 MX3]].
  assert (NewOutside:forall bi,In bi [by1;by2;by3] -> ~In bi [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC]).
  { intros bi Member Old;exact (swu_nodup_app_apart [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC]
      [by1;by2;by3] Sep bi Old Member). }
  assert (SepR:NoDup [bA;bB;bC;by1;by2;by3]) by
    (exact (@NoDup_app_remove_l block [bt;bw;ba;bx;bj;bb;bc] [bA;bB;bC;by1;by2;by3] Sep)).
  pose proof Free as All0;rewrite Forall_forall in All0.
  pose proof FreeS as AllS;rewrite Forall_forall in AllS.
  assert (FreeR:Forall (fun bi=>Mem.range_perm ms bi 0 40 Cur Freeable) [bA;bB;bC;by1;by2;by3]).
  { change (Forall (fun bi=>Mem.range_perm ms bi 0 40 Cur Freeable) ([bA;bB;bC]++[by1;by2;by3])).
    apply Forall_app;split;rewrite Forall_forall;intros bi Member.
    - apply AllS;clear -Member;cbn [In] in *;tauto.
    - eapply curve_keep_free;[lia|apply All0;clear -Member;cbn [In] in *;tauto|exact FS|].
      intros;apply NewOutside;exact Member. }
  destruct (exec_swu_roots e le ms bA bB bC by1 by2 by3 (swu_alpha_words w inv)
    (swu_beta_words w inv) (swu_gamma_words w inv) (swu_radicand x1)
    (swu_radicand (@literal_fe_negate Alg.CoreFunSem (@literal_fe_add Alg.CoreFunSem
      (x1,@literal_fe_one256 Alg.CoreFunSem tt)))) (swu_radicand x3)
    ERoot EAlpha EBeta EGamma EY1 EY2 EY3 SepR MA MB MC Alpha Beta Gamma FreeR)
    as (mf & Roots & Y1 & Y2 & Y3 & FreeRoots & YBounds & VY1 & VY2 & VY3 & CY1 & CY2 & CY3 & FR & RR).
  assert (Safe:forall bi,In bi [bt;ba;bb;bc] -> ~In bi [bA;bB;bC;by1;by2;by3]).
  { intros bi Member;eapply (swu_nodup_app_apart [bt;bw;ba;bx;bj;bb;bc] [bA;bB;bC;by1;by2;by3] Sep).
    clear -Member;cbn [In] in *;tauto. }
  assert (Keep:forall bi rho,In bi [bt;ba;bb;bc] -> fe_at ms bi 0 (words5 rho) -> fe_at mf bi 0 (words5 rho)).
  { intros bi rho Member Field;eapply curve_keep_field_range;
      [reflexivity|exact Field|exact FR|];intros;apply Safe;exact Member. }
  assert (TF:fe_at mf bt 0 (words5 w)) by (eapply Keep;[left;reflexivity|exact TS]).
  assert (AF:fe_at mf ba 0 (words5 (swu_input_first_words w inv))) by
    (eapply Keep;[right;left;reflexivity|exact AS]).
  assert (BF:fe_at mf bb 0 (words5 (swu_second_words (swu_input_first_words w inv)))) by
    (eapply Keep;[do 2 right;left;reflexivity|exact BS]).
  assert (CF:fe_at mf bc 0 (words5 (swu_input_third_words w inv))) by
    (eapply Keep;[do 3 right;left;reflexivity|exact CS]).
  assert (FreeF:Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable)
    [bt;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]).
  { rewrite Forall_forall in FreeRoots|-*;intros bi Member.
    destruct (in_dec Pos.eq_dec bi [bA;bB;bC;by1;by2;by3]) as [Touched|Outside].
    - apply FreeRoots;exact Touched.
    - eapply curve_keep_free;[lia| |exact FR|intros;exact Outside].
      apply AllS;clear -Member Outside;cbn [In] in *;tauto. }
  assert (TightY:Forall mul_small_input_bounds
    [root_chain_candidate (swu_alpha_words w inv);root_chain_candidate (swu_beta_words w inv);
     root_chain_candidate (swu_gamma_words w inv)]).
  { constructor;[exact (root_chain_candidate_tight _ _ MA)|].
    constructor;[exact (root_chain_candidate_tight _ _ MB)|].
    constructor;[exact (root_chain_candidate_tight _ _ MC)|constructor]. }
  exists inv,mf;split.
  - unfold swu_through_roots,swu_through_roots_statements.
    change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence swu_through_cubics_statements swu_roots_prefix) E0
      (swu_selection_temps w inv le) mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Start|exact Roots].
  - split;[exact TF|];split;[exact AF|];split;[exact BF|];split;[exact CF|];
      split;[exact Y1|];split;[exact Y2|];split;[exact Y3|];split;[exact FreeF|];split.
    + constructor;[exact ABounds|];constructor;[exact BBounds|];constructor;[exact CBounds|exact YBounds].
    + split;[exact TightY|];split;[eapply swu_startup_preserved;[exact ReadyS|exact RR] | ];split.
      * eapply lframe_trans with (m2:=ms).
        { eapply lframe_implies;[exact FS|];intros bi pos Outside Valid;clear -Outside;cbn [In] in *;tauto. }
        eapply lframe_implies;[exact FR|];intros bi pos Outside Valid;clear -Outside;cbn [In] in *;tauto.
      * split;[eapply preserved_trans;[exact RS|exact RR] | ].
        split;[exact MX1|];split;[exact MX2|];split;[exact MX3|];split;[exact VY1|];
          split;[exact VY2|];split;[exact VY3|];split;[exact CY1|];split;[exact CY2|exact CY3].
Qed.

(** The original square/multiply/add-seven radicand computation, shared by
    all three SWU candidates. Inputs need only the existing loose bounds;
    output storage need not be initialized. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep
  Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_initial C.jet_secp_swu_first_candidate C.jet_secp_swu_second_candidate C.jet_secp_swu_third_candidate
  C.jet_secp_swu_constant_product C.jet_secp_field_pair_multiply C.jet_secp_field_mul_small
  C.jet_secp_field_add_int C.jet_secp_field_sum_bounds C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_square_separate_caller
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_fns C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_cubic_square (r a:ident) :=
  curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
    [curve_local_address r;curve_local_address a].
Definition swu_cubic_multiply (r a:ident) :=
  curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
    [curve_local_address r;curve_local_address r;curve_local_address a].
Definition swu_cubic_add (r:ident) :=
  curve_call _secp256k1_fe_add_int f_secp256k1_fe_add_int None
    [curve_local_address r;Econst_int (Int.repr 7) tint].
Definition swu_cubic_statements r a :=
  [swu_cubic_square r a;swu_cubic_multiply r a;swu_cubic_add r].
Definition swu_cubic_prefix r a := statement_sequence (swu_cubic_statements r a) Sskip.
Definition swu_cubic_words w := add_int_words (Int.repr 7) (field_pair_product (square_words w) w).

Lemma exec_swu_cubic_square_call r a e le m mf br ba :
  e!_secp256k1_fe_sqr=None -> e!r=Some (br,curve_fe_type) -> e!a=Some (ba,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (swu_cubic_square r a) E0 le mf Out_normal.
Proof.
  intros Fun R A Call;unfold swu_cubic_square;eapply exec_curve_call with
    (vargs:=[Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact A|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_cubic_multiply_call r a e le m mf br ba :
  e!_secp256k1_fe_mul=None -> e!r=Some (br,curve_fe_type) -> e!a=Some (ba,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (swu_cubic_multiply r a) E0 le mf Out_normal.
Proof.
  intros Fun R A Call;unfold swu_cubic_multiply;eapply exec_curve_call with
    (vargs:=[Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact A|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_cubic_add_call r e le m mf br :
  e!_secp256k1_fe_add_int=None -> e!r=Some (br,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr br Ptrofs.zero;Vint (Int.repr 7)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (swu_cubic_add r) E0 le mf Out_normal.
Proof.
  intros Fun R Call;unfold swu_cubic_add;eapply exec_curve_call with
    (vargs:=[Vptr br Ptrofs.zero;Vint (Int.repr 7)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.

Theorem exec_swu_cubic r a e le m br ba w :
  e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add_int=None ->
  e!r=Some (br,curve_fe_type) -> e!a=Some (ba,curve_fe_type) -> br<>ba ->
  square_input_bounds w -> fe_at m ba 0 (words5 w) ->
  Mem.range_perm m br 0 40 Cur Freeable -> Mem.range_perm m ba 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (swu_cubic_prefix r a) E0 le mf Out_normal /\
  fe_at mf br 0 (words5 (swu_cubic_words w)) /\ fe_at mf ba 0 (words5 w) /\
  Mem.range_perm mf br 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
  field_scaled_bounds 2 (swu_cubic_words w) /\ square_input_bounds (swu_cubic_words w) /\
  eqm feP (radix_value (swu_cubic_words w)) (swu_cubic (radix_value w)) /\
  lframe (fun b _=>b<>br /\ b<>ba) m mf /\ readonly_preserved m mf.
Proof.
  intros ES EM EA ER EX Ne Bounds Input FR FA.
  destruct (eval_square_separate_from_storage w m br ba Bounds FR Input FA Ne)
    as (m1 & Square & R1 & FR1 & A1 & FA1 & VQ & B1 & F1).
  destruct (eval_field_pair_multiply (square_words w) w m1 br ba B1 Bounds Ne R1 A1 FR1 FA1)
    as (m2 & Mul & R2 & A2 & FR2 & FA2 & VM & B2 & Tight2 & F2).
  assert (Tight:mul_small_input_bounds (field_pair_product (square_words w) w)) by
    (intros i Index;exact (proj2 (Tight2 i Index))).
  destruct (eval_field_add_int_small (Int.repr 7) (field_pair_product (square_words w) w) m2 br
    ltac:(change (0<=7<=8);lia) Tight R2 FR2)
    as (mf & Add & RF & FRF & AddValue & OutBounds & F3).
  assert (AF:fe_at mf ba 0 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact A2|exact F3|];intros;congruence).
  assert (FAF:Mem.range_perm mf ba 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FA2|exact F3|];intros;congruence).
  assert (Scaled:field_scaled_bounds 2 (swu_cubic_words w)) by
    (apply swu_add_int_scaled;[change (0<=7<=8);lia|exact Tight]).
  rewrite field_prime_matches_normalizer in VQ,VM.
  assert (Value:eqm feP (radix_value (swu_cubic_words w)) (swu_cubic (radix_value w))).
  { unfold swu_cubic_words;rewrite AddValue;change (Int.signed (Int.repr 7)) with 7.
    unfold swu_cubic;replace (radix_value w^3) with (radix_value w*radix_value w*radix_value w) by ring.
    apply Zplus_eqm;[|reflexivity];eapply eqm_trans;[exact VM|].
    apply Zmult_eqm;[exact VQ|reflexivity]. }
  assert (RQ:readonly_preserved m m1) by
    (eapply secp_closed_function_preserved;[exact swu_square_closed|reflexivity|exact Square]).
  assert (RM:readonly_preserved m1 m2) by
    (eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Mul]).
  assert (RA:readonly_preserved m2 mf) by
    (eapply (secp_closed_function_preserved f_secp256k1_fe_add_int);[reflexivity|reflexivity|exact Add]).
  exists mf;split.
  - unfold swu_cubic_prefix,swu_cubic_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);
      [eapply exec_swu_cubic_square_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m2);
      [eapply exec_swu_cubic_multiply_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);
      [eapply exec_swu_cubic_add_call;eassumption|apply exec_Sskip].
  - split;[exact RF|];split;[exact AF|];split;[exact FRF|];split;[exact FAF|];
      split;[exact Scaled|];split;[exact OutBounds|];split;[exact Value|];split.
    + eapply lframe_trans with (m2:=m1);[exact F1|].
      eapply lframe_trans with (m2:=m2);[exact F2|].
      eapply lframe_implies;[exact F3|];intros b pos [NR NA] Valid;exact NR.
    + eapply preserved_trans;[exact RQ|];eapply preserved_trans;[exact RM|exact RA].
Qed.
Lemma swu_cubic_spec_match value x a :
  eqm feP value (swu_cubic x) -> eqm feP x a -> eqm feP value (swu_cubic a).
Proof.
  intros Value X;eapply eqm_trans;[exact Value|];unfold swu_cubic.
  replace (x^3) with (x*x*x) by ring;replace (a^3) with (a*a*a) by ring.
  apply Zplus_eqm;[|reflexivity];apply Zmult_eqm;[apply Zmult_eqm;exact X|exact X].
Qed.

Definition swu_cubics_statements := swu_cubic_statements _alphain _x1++
  swu_cubic_statements _betain _x2++swu_cubic_statements _gammain _x3.
Definition swu_cubics_prefix := statement_sequence swu_cubics_statements Sskip.
Definition swu_after_cubics := match swu_after_third_candidate with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
      (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest))))))))=>rest | _=>Sskip end.
Lemma swu_cubics_source : swu_after_third_candidate=
  statement_sequence swu_cubics_statements swu_after_cubics.
Proof. reflexivity. Qed.

Lemma swu_two_keep_free m mf br ba blocks :
  lframe (fun b _=>b<>br /\ b<>ba) m mf ->
  Mem.range_perm mf br 0 40 Cur Freeable -> Mem.range_perm mf ba 0 40 Cur Freeable ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) blocks ->
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) blocks.
Proof.
  intros Frame FR FA Free;rewrite Forall_forall in *;intros b Member.
  destruct (Pos.eq_dec b br) as [->|NR];[exact FR|].
  destruct (Pos.eq_dec b ba) as [->|NA];[exact FA|].
  eapply curve_keep_free;[lia|apply Free;exact Member|exact Frame|];intros;split;assumption.
Qed.
Lemma swu_two_keep_field m mf br ba b w : b<>br -> b<>ba ->
  fe_at m b 0 (words5 w) -> lframe (fun b _=>b<>br /\ b<>ba) m mf ->
  fe_at mf b 0 (words5 w).
Proof.
  intros NR NA Field Frame;eapply curve_keep_field_range;
    [reflexivity|exact Field|exact Frame|];intros;split;assumption.
Qed.

Theorem exec_swu_cubics e le m ba bb bc bA bB bC a b c :
  e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add_int=None ->
  e!_x1=Some (ba,curve_fe_type) -> e!_x2=Some (bb,curve_fe_type) -> e!_x3=Some (bc,curve_fe_type) ->
  e!_alphain=Some (bA,curve_fe_type) -> e!_betain=Some (bB,curve_fe_type) ->
  e!_gammain=Some (bC,curve_fe_type) -> NoDup [ba;bb;bc;bA;bB;bC] ->
  square_input_bounds a -> square_input_bounds b -> square_input_bounds c ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) -> fe_at m bc 0 (words5 c) ->
  Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [ba;bb;bc;bA;bB;bC] -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_cubics_prefix E0 le mf Out_normal /\
  fe_at mf ba 0 (words5 a) /\ fe_at mf bb 0 (words5 b) /\ fe_at mf bc 0 (words5 c) /\
  fe_at mf bA 0 (words5 (swu_cubic_words a)) /\
  fe_at mf bB 0 (words5 (swu_cubic_words b)) /\
  fe_at mf bC 0 (words5 (swu_cubic_words c)) /\
  Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [ba;bb;bc;bA;bB;bC] /\
  field_scaled_bounds 2 (swu_cubic_words a) /\ square_input_bounds (swu_cubic_words a) /\
  field_scaled_bounds 2 (swu_cubic_words b) /\ square_input_bounds (swu_cubic_words b) /\
  field_scaled_bounds 2 (swu_cubic_words c) /\ square_input_bounds (swu_cubic_words c) /\
  eqm feP (radix_value (swu_cubic_words a)) (swu_cubic (radix_value a)) /\
  eqm feP (radix_value (swu_cubic_words b)) (swu_cubic (radix_value b)) /\
  eqm feP (radix_value (swu_cubic_words c)) (swu_cubic (radix_value c)) /\
  lframe (fun bi _=>~In bi [ba;bb;bc;bA;bB;bC]) m mf /\ readonly_preserved m mf.
Proof.
  intros ES EM EA EX1 EX2 EX3 EAlpha EBeta EGamma Sep BA BB BC A B C Free.
  assert (Distinct:ba<>bb /\ ba<>bc /\ ba<>bA /\ ba<>bB /\ ba<>bC /\
    bb<>bc /\ bb<>bA /\ bb<>bB /\ bb<>bC /\ bc<>bA /\ bc<>bB /\ bc<>bC /\
    bA<>bB /\ bA<>bC /\ bB<>bC) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Distinct as (AB & AC & AA & AB' & AC' & BC' & BA' & BB' & BC'' & CA & CB & CC & ABl & ACl & BCl).
  pose proof Free as Free0;rewrite Forall_forall in Free0.
  destruct (exec_swu_cubic _alphain _x1 e le m bA ba a ES EM EA EAlpha EX1 ltac:(congruence)
    BA A (Free0 bA ltac:(cbn;tauto)) (Free0 ba ltac:(cbn;tauto)))
    as (m1 & Alpha & RA1 & A1 & FRA1 & FA1 & SA & OA & VA & F1 & R1).
  assert (Free1:Forall (fun bi=>Mem.range_perm m1 bi 0 40 Cur Freeable) [ba;bb;bc;bA;bB;bC]) by
    (eapply swu_two_keep_free;[exact F1|exact FRA1|exact FA1|exact Free]).
  pose proof Free1 as All1;rewrite Forall_forall in All1.
  assert (B1:fe_at m1 bb 0 (words5 b)) by
    (eapply swu_two_keep_field;[| |exact B|exact F1];congruence).
  assert (C1:fe_at m1 bc 0 (words5 c)) by
    (eapply swu_two_keep_field;[| |exact C|exact F1];congruence).
  destruct (exec_swu_cubic _betain _x2 e le m1 bB bb b ES EM EA EBeta EX2 ltac:(congruence)
    BB B1 (All1 bB ltac:(cbn;tauto)) (All1 bb ltac:(cbn;tauto)))
    as (m2 & Beta & RB2 & B2 & FRB2 & FB2 & SB & OB & VB & F2 & R2).
  assert (Free2:Forall (fun bi=>Mem.range_perm m2 bi 0 40 Cur Freeable) [ba;bb;bc;bA;bB;bC]) by
    (eapply swu_two_keep_free;[exact F2|exact FRB2|exact FB2|exact Free1]).
  pose proof Free2 as All2;rewrite Forall_forall in All2.
  assert (C2:fe_at m2 bc 0 (words5 c)) by
    (eapply swu_two_keep_field;[| |exact C1|exact F2];congruence).
  assert (A2:fe_at m2 ba 0 (words5 a)) by
    (eapply swu_two_keep_field;[| |exact A1|exact F2];congruence).
  assert (RA2:fe_at m2 bA 0 (words5 (swu_cubic_words a))) by
    (eapply swu_two_keep_field;[| |exact RA1|exact F2];congruence).
  destruct (exec_swu_cubic _gammain _x3 e le m2 bC bc c ES EM EA EGamma EX3 ltac:(congruence)
    BC C2 (All2 bC ltac:(cbn;tauto)) (All2 bc ltac:(cbn;tauto)))
    as (mf & Gamma & RCF & CF & FRCF & FCF & SC & OC & VC & F3 & R3).
  assert (FreeF:Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [ba;bb;bc;bA;bB;bC]) by
    (eapply swu_two_keep_free;[exact F3|exact FRCF|exact FCF|exact Free2]).
  assert (AF:fe_at mf ba 0 (words5 a)) by
    (eapply swu_two_keep_field;[| |exact A2|exact F3];congruence).
  assert (BF:fe_at mf bb 0 (words5 b)) by
    (eapply swu_two_keep_field;[| |exact B2|exact F3];congruence).
  assert (RAF:fe_at mf bA 0 (words5 (swu_cubic_words a))) by
    (eapply swu_two_keep_field;[| |exact RA2|exact F3];congruence).
  assert (RBF:fe_at mf bB 0 (words5 (swu_cubic_words b))) by
    (eapply swu_two_keep_field;[| |exact RB2|exact F3];congruence).
  exists mf;split.
  - unfold swu_cubics_prefix,swu_cubics_statements.
    change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence (swu_cubic_statements _alphain _x1)
        (statement_sequence (swu_cubic_statements _betain _x2) (swu_cubic_prefix _gammain _x3)))
      E0 le mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Alpha|].
    eapply exec_statement_prefix_then_last;[exact Beta|exact Gamma].
  - split;[exact AF|];split;[exact BF|];split;[exact CF|];split;[exact RAF|];split;[exact RBF|];
      split;[exact RCF|];split;[exact FreeF|];split;[exact SA|];split;[exact OA|];
      split;[exact SB|];split;[exact OB|];split;[exact SC|];split;[exact OC|];
      split;[exact VA|];split;[exact VB|];split;[exact VC|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact F1|];intros bi pos Outside Valid;
          split;intro Same;apply Outside;subst;cbn;tauto.
      * eapply lframe_trans with (m2:=m2).
        { eapply lframe_implies;[exact F2|];intros bi pos Outside Valid;
            split;intro Same;apply Outside;subst;cbn;tauto. }
        eapply lframe_implies;[exact F3|];intros bi pos Outside Valid;
          split;intro Same;apply Outside;subst;cbn;tauto.
    + eapply preserved_trans;[exact R1|];eapply preserved_trans;[exact R2|exact R3].
Qed.

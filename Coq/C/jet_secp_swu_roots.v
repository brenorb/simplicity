(** Execute the three original SWU square-root calls, including the two
    generated call-result assignments. The helper's checked loose-input
    contract supplies execution, candidate values and exact check flags. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep
  Integers Memory Values Events Maps.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_swu_cubics C.jet_secp_swu_before_roots C.jet_secp_swu_startup
  C.jet_secp_root_function C.jet_secp_root_function_literal C.jet_secp_root_check
  C.jet_secp_root_literal C.jet_secp_root_chain_numeric C.jet_secp_rescale_literal
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_fns C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_chain_candidate literal_root_candidate rescale_field_output.

Definition swu_root_call result r a := curve_call _secp256k1_fe_sqrt_var f_secp256k1_fe_sqrt_var
  result [curve_local_address r;curve_local_address a].
Definition swu_root_step (save:option (ident*ident)) r a := match save with
  | Some (tmp,flag)=>Ssequence (swu_root_call (Some tmp) r a) (Sset flag (Etempvar tmp tint))
  | None=>swu_root_call None r a end.
Definition swu_root_value w := Vint (if root_check_flag w then Int.one else Int.zero).
Definition swu_root_temps (save:option (ident*ident)) w le := match save with
  | Some (tmp,flag)=>PTree.set flag (swu_root_value w) (PTree.set tmp (swu_root_value w) le)
  | None=>le end.
Definition swu_roots_statements :=
  [swu_root_step (Some (_t'1,_alphaquad)) _y1 _alphain;
   swu_root_step (Some (_t'2,_betaquad)) _y2 _betain;
   swu_root_step None _y3 _gammain].
Definition swu_roots_prefix := statement_sequence swu_roots_statements Sskip.
Definition swu_after_roots := match swu_after_cubics with
  | Ssequence _ (Ssequence _ (Ssequence _ rest))=>rest | _=>Sskip end.
Lemma swu_roots_source : swu_after_cubics=
  statement_sequence swu_roots_statements swu_after_roots.
Proof. reflexivity. Qed.
Lemma swu_root_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_sqrt_var)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.

Lemma exec_swu_root_call result r a e le m mf br ba w :
  e!_secp256k1_fe_sqrt_var=None -> e!r=Some (br,curve_fe_type) -> e!a=Some (ba,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqrt_var)
    [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf (swu_root_value w) ->
  Clight2.exec_stmt secp_ge e le m (swu_root_call result r a) E0
    (set_opttemp result (swu_root_value w) le) mf Out_normal.
Proof.
  intros Fun R A Call;unfold swu_root_call;eapply exec_curve_call with
    (vargs:=[Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=swu_root_value w).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact A|reflexivity|constructor].
  - exact Call.
Qed.

Theorem exec_swu_root_step save r a e le m br ba w (x:Ty.tySem (Word 8)) :
  e!_secp256k1_fe_sqrt_var=None -> e!r=Some (br,curve_fe_type) -> e!a=Some (ba,curve_fe_type) ->
  ba<>br -> root_words_match w x -> fe_at m ba 0 (words5 w) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (swu_root_step save r a) E0
    (swu_root_temps save w le) mf Out_normal /\
  fe_at mf br 0 (words5 (root_chain_candidate w)) /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  square_input_bounds (root_chain_candidate w) /\
  rescale_field_output (root_chain_candidate w)=literal_root_candidate x /\
  root_check_flag w=Bit.toBool (literal_root_check x) /\
  lframe (fun b _=>b<>ba /\ b<>br) m mf /\ readonly_preserved m mf.
Proof.
  intros Fun R A Ne Match Field FA FR.
  destruct (eval_root_function w x m br ba Ne Match Field FA FR)
    as (mf & Call & Root & FAF & FRF & Frame).
  assert (ReadOnly:readonly_preserved m mf) by
    (eapply (secp_closed_function_preserved f_secp256k1_fe_sqrt_var);
     [exact swu_root_closed|reflexivity|exact Call]).
  exists mf;split.
  - destruct save as [[tmp flag] | ];unfold swu_root_step,swu_root_temps.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
        (le1:=PTree.set tmp (swu_root_value w) le).
      * eapply (exec_swu_root_call (Some tmp));eassumption.
      * apply exec_Sset;unfold swu_root_value;apply eval_Etempvar;apply PTree.gss.
    + eapply (exec_swu_root_call None);eassumption.
  - split;[exact Root|];split;[exact FAF|];split;[exact FRF|];split.
    + exact (proj1 (root_chain_candidate_matches w x Match)).
    + split;[apply root_candidate_output;exact Match|];split;
        [apply root_check_flag_matches;exact Match|];split;assumption.
Qed.

Definition swu_roots_temps a b le :=
  swu_root_temps (Some (_t'2,_betaquad)) b
    (swu_root_temps (Some (_t'1,_alphaquad)) a le).
Lemma swu_roots_temps_alpha a b le :
  (swu_roots_temps a b le)!_alphaquad=Some (swu_root_value a).
Proof.
  unfold swu_roots_temps,swu_root_temps;
    rewrite !PTree.gso by discriminate;apply PTree.gss.
Qed.
Lemma swu_roots_temps_beta a b le :
  (swu_roots_temps a b le)!_betaquad=Some (swu_root_value b).
Proof. apply PTree.gss. Qed.
Lemma swu_roots_temps_other a b le id :
  id<>_alphaquad -> id<>_t'1 -> id<>_betaquad -> id<>_t'2 ->
  (swu_roots_temps a b le)!id=le!id.
Proof.
  intros;unfold swu_roots_temps,swu_root_temps;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem exec_swu_roots e le m bA bB bC by1 by2 by3 a b c (x y z:Ty.tySem (Word 8)) :
  e!_secp256k1_fe_sqrt_var=None ->
  e!_alphain=Some (bA,curve_fe_type) -> e!_betain=Some (bB,curve_fe_type) ->
  e!_gammain=Some (bC,curve_fe_type) -> e!_y1=Some (by1,curve_fe_type) ->
  e!_y2=Some (by2,curve_fe_type) -> e!_y3=Some (by3,curve_fe_type) ->
  NoDup [bA;bB;bC;by1;by2;by3] ->
  root_words_match a x -> root_words_match b y -> root_words_match c z ->
  fe_at m bA 0 (words5 a) -> fe_at m bB 0 (words5 b) -> fe_at m bC 0 (words5 c) ->
  Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [bA;bB;bC;by1;by2;by3] -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_roots_prefix E0 (swu_roots_temps a b le) mf Out_normal /\
  fe_at mf by1 0 (words5 (root_chain_candidate a)) /\
  fe_at mf by2 0 (words5 (root_chain_candidate b)) /\
  fe_at mf by3 0 (words5 (root_chain_candidate c)) /\
  Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [bA;bB;bC;by1;by2;by3] /\
  Forall square_input_bounds [root_chain_candidate a;root_chain_candidate b;root_chain_candidate c] /\
  rescale_field_output (root_chain_candidate a)=literal_root_candidate x /\
  rescale_field_output (root_chain_candidate b)=literal_root_candidate y /\
  rescale_field_output (root_chain_candidate c)=literal_root_candidate z /\
  root_check_flag a=Bit.toBool (literal_root_check x) /\
  root_check_flag b=Bit.toBool (literal_root_check y) /\
  root_check_flag c=Bit.toBool (literal_root_check z) /\
  lframe (fun bi _=>~In bi [bA;bB;bC;by1;by2;by3]) m mf /\ readonly_preserved m mf.
Proof.
  intros Fun EA EB EC EY1 EY2 EY3 Sep MA MB MC A B C Free.
  assert (Distinct:bA<>bB /\ bA<>bC /\ bA<>by1 /\ bA<>by2 /\ bA<>by3 /\
    bB<>bC /\ bB<>by1 /\ bB<>by2 /\ bB<>by3 /\ bC<>by1 /\ bC<>by2 /\ bC<>by3 /\
    by1<>by2 /\ by1<>by3 /\ by2<>by3) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Distinct as (AB & AC & AY1 & AY2 & AY3 & BC & BY1 & BY2 & BY3 & CY1 & CY2 & CY3 & Y12 & Y13 & Y23).
  pose proof Free as All0;rewrite Forall_forall in All0.
  destruct (exec_swu_root_step (Some (_t'1,_alphaquad)) _y1 _alphain e le m by1 bA a x
    Fun EY1 EA AY1 MA A (All0 bA ltac:(left;reflexivity))
    (All0 by1 ltac:(do 3 right;left;reflexivity)))
    as (m1 & Alpha & Y1 & FA1 & FY1 & BA & VA & CA & F1 & R1).
  assert (Free1:Forall (fun bi=>Mem.range_perm m1 bi 0 40 Cur Freeable) [bA;bB;bC;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F1|exact FA1|exact FY1|exact Free]).
  pose proof Free1 as All1;rewrite Forall_forall in All1.
  assert (B1:fe_at m1 bB 0 (words5 b)) by
    (eapply swu_two_keep_field;[| |exact B|exact F1];congruence).
  assert (C1:fe_at m1 bC 0 (words5 c)) by
    (eapply swu_two_keep_field;[| |exact C|exact F1];congruence).
  destruct (exec_swu_root_step (Some (_t'2,_betaquad)) _y2 _betain e
    (swu_root_temps (Some (_t'1,_alphaquad)) a le) m1 by2 bB b y Fun EY2 EB BY2 MB B1
    (All1 bB ltac:(right;left;reflexivity)) (All1 by2 ltac:(do 4 right;left;reflexivity)))
    as (m2 & Beta & Y2 & FB2 & FY2 & BB & VB & CB & F2 & R2).
  assert (Free2:Forall (fun bi=>Mem.range_perm m2 bi 0 40 Cur Freeable) [bA;bB;bC;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F2|exact FB2|exact FY2|exact Free1]).
  pose proof Free2 as All2;rewrite Forall_forall in All2.
  assert (C2:fe_at m2 bC 0 (words5 c)) by
    (eapply swu_two_keep_field;[| |exact C1|exact F2];congruence).
  assert (Y1M2:fe_at m2 by1 0 (words5 (root_chain_candidate a))) by
    (eapply swu_two_keep_field;[| |exact Y1|exact F2];congruence).
  destruct (exec_swu_root_step None _y3 _gammain e (swu_roots_temps a b le) m2 by3 bC c z
    Fun EY3 EC CY3 MC C2 (All2 bC ltac:(do 2 right;left;reflexivity))
    (All2 by3 ltac:(do 5 right;left;reflexivity)))
    as (mf & Gamma & Y3 & FCF & FY3 & BC' & VC & CC & F3 & R3).
  assert (FreeF:Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [bA;bB;bC;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F3|exact FCF|exact FY3|exact Free2]).
  assert (Y1F:fe_at mf by1 0 (words5 (root_chain_candidate a))) by
    (eapply swu_two_keep_field;[| |exact Y1M2|exact F3];congruence).
  assert (Y2F:fe_at mf by2 0 (words5 (root_chain_candidate b))) by
    (eapply swu_two_keep_field;[| |exact Y2|exact F3];congruence).
  exists mf;split.
  - unfold swu_roots_prefix,swu_roots_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1)
      (le1:=swu_root_temps (Some (_t'1,_alphaquad)) a le);[exact Alpha|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2)
      (le1:=swu_roots_temps a b le);[exact Beta|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
      (le1:=swu_roots_temps a b le);[exact Gamma|apply exec_Sskip].
  - split;[exact Y1F|];split;[exact Y2F|];split;[exact Y3|];split;[exact FreeF|];
      split;[repeat constructor;assumption|];split;[exact VA|];split;[exact VB|];
      split;[exact VC|];split;[exact CA|];split;[exact CB|];split;[exact CC|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact F1|];intros bi pos Outside Valid;
          split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto.
      * eapply lframe_trans with (m2:=m2).
        { eapply lframe_implies;[exact F2|];intros bi pos Outside Valid;
            split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto. }
        eapply lframe_implies;[exact F3|];intros bi pos Outside Valid;
          split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto.
    + eapply preserved_trans;[exact R1|];eapply preserved_trans;[exact R2|exact R3].
Qed.


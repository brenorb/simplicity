(** The four original SWU conditional moves. Flags are evaluated as the
    original C boolean/bitwise expressions, not supplied as call oracles. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Cop Clight Clightdefs ClightBigstep
  Integers Memory Values Events Maps.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_field_cmov C.jet_secp_swu_cubics C.jet_secp_swu_roots
  C.jet_secp_swu_before_selection C.jet_secp_swu_startup
  C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_statement_prefix C.jet_secp_fns C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_select_flag (third:bool) := Ebinop Oand
  (Eunop Onotbool (Etempvar _alphaquad tint) tint)
  (if third then Eunop Onotbool (Etempvar _betaquad tint) tint else Etempvar _betaquad tint) tint.
Definition swu_select_call (third y:bool) := curve_call _secp256k1_fe_cmov f_secp256k1_fe_cmov None
  [curve_local_address (if y then _y1 else _x1);
   curve_local_address (if third then (if y then _y3 else _x3) else (if y then _y2 else _x2));
   swu_select_flag third].
Definition swu_select_statements :=
  [swu_select_call false false;swu_select_call false true;
   swu_select_call true false;swu_select_call true true].
Definition swu_select_prefix := statement_sequence swu_select_statements Sskip.
Definition swu_after_select := match swu_after_roots with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest)))=>rest | _=>Sskip end.
Definition swu_select_bool (third alpha beta:bool) := andb (negb alpha) (if third then negb beta else beta).
Definition swu_selected_words (alpha beta:bool) (a b c:nat->int64) := if alpha then a else if beta then b else c.
Lemma swu_select_source : swu_after_roots=
  statement_sequence swu_select_statements swu_after_select.
Proof. reflexivity. Qed.

Lemma eval_swu_select_flag third alpha beta e le m :
  le!_alphaquad=Some (Vint (cmov_int alpha)) -> le!_betaquad=Some (Vint (cmov_int beta)) ->
  eval_expr secp_ge e le m (swu_select_flag third) (Vint (cmov_int (swu_select_bool third alpha beta))).
Proof.
  intros A B;unfold swu_select_flag.
  eapply eval_Ebinop with (v1:=Vint (cmov_int (negb alpha)))
    (v2:=Vint (cmov_int (if third then negb beta else beta))).
  - eapply eval_Eunop with (v1:=Vint (cmov_int alpha));[apply eval_Etempvar;exact A|].
    destruct alpha;reflexivity.
  - destruct third.
    + eapply eval_Eunop with (v1:=Vint (cmov_int beta));[apply eval_Etempvar;exact B|].
      destruct beta;reflexivity.
    + apply eval_Etempvar;exact B.
  - destruct third,alpha,beta;reflexivity.
Qed.
Lemma exec_swu_select_call (third y alpha beta:bool) e le m mf bo bi :
  e!_secp256k1_fe_cmov=None -> e!(if y then _y1 else _x1)=Some (bo,curve_fe_type) ->
  e!(if third then (if y then _y3 else _x3) else (if y then _y2 else _x2))=Some (bi,curve_fe_type) ->
  le!_alphaquad=Some (Vint (cmov_int alpha)) -> le!_betaquad=Some (Vint (cmov_int beta)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_cmov)
    [Vptr bo Ptrofs.zero;Vptr bi Ptrofs.zero;Vint (cmov_int (swu_select_bool third alpha beta))]
    E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (swu_select_call third y) E0 le mf Out_normal.
Proof.
  intros Fun O I A B Call;unfold swu_select_call;eapply exec_curve_call with
    (vargs:=[Vptr bo Ptrofs.zero;Vptr bi Ptrofs.zero;Vint (cmov_int (swu_select_bool third alpha beta))]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact O|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact I|reflexivity|].
    eapply eval_Econs;[apply (eval_swu_select_flag third alpha beta);assumption|reflexivity|constructor].
  - exact Call.
Qed.
Lemma swu_selected_words_compose alpha beta a b c :
  (if swu_select_bool true alpha beta then c else if swu_select_bool false alpha beta then b else a)=
  swu_selected_words alpha beta a b c.
Proof. destruct alpha,beta;reflexivity. Qed.

Theorem exec_swu_select alpha beta e le m bx1 bx2 bx3 by1 by2 by3 x1 x2 x3 y1 y2 y3 :
  e!_secp256k1_fe_cmov=None -> e!_x1=Some (bx1,curve_fe_type) -> e!_x2=Some (bx2,curve_fe_type) ->
  e!_x3=Some (bx3,curve_fe_type) -> e!_y1=Some (by1,curve_fe_type) ->
  e!_y2=Some (by2,curve_fe_type) -> e!_y3=Some (by3,curve_fe_type) ->
  le!_alphaquad=Some (Vint (cmov_int alpha)) -> le!_betaquad=Some (Vint (cmov_int beta)) ->
  NoDup [bx1;bx2;bx3;by1;by2;by3] ->
  fe_at m bx1 0 (words5 x1) -> fe_at m bx2 0 (words5 x2) -> fe_at m bx3 0 (words5 x3) ->
  fe_at m by1 0 (words5 y1) -> fe_at m by2 0 (words5 y2) -> fe_at m by3 0 (words5 y3) ->
  Forall (fun bi=>Mem.range_perm m bi 0 40 Cur Freeable) [bx1;bx2;bx3;by1;by2;by3] -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_select_prefix E0 le mf Out_normal /\
  fe_at mf bx1 0 (words5 (swu_selected_words alpha beta x1 x2 x3)) /\
  fe_at mf by1 0 (words5 (swu_selected_words alpha beta y1 y2 y3)) /\
  Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [bx1;bx2;bx3;by1;by2;by3] /\
  lframe (fun bi _=>~In bi [bx1;bx2;bx3;by1;by2;by3]) m mf /\ readonly_preserved m mf.
Proof.
  intros Fun EX1 EX2 EX3 EY1 EY2 EY3 A B Sep X1 X2 X3 Y1 Y2 Y3 Free.
  assert (Distinct:bx1<>bx2 /\ bx1<>bx3 /\ bx1<>by1 /\ bx1<>by2 /\ bx1<>by3 /\
    bx2<>bx3 /\ bx2<>by1 /\ bx2<>by2 /\ bx2<>by3 /\ bx3<>by1 /\ bx3<>by2 /\ bx3<>by3 /\
    by1<>by2 /\ by1<>by3 /\ by2<>by3) by
    (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Distinct as (X12 & X13 & XY11 & XY12 & XY13 & X23 & XY21 & XY22 & XY23 & XY31 & XY32 & XY33 & Y12 & Y13 & Y23).
  pose proof Free as All0;rewrite Forall_forall in All0.
  destruct (eval_field_cmov (swu_select_bool false alpha beta) x1 x2 m bx1 bx2 X12 X1 X2
    (All0 bx1 ltac:(left;reflexivity)) (All0 bx2 ltac:(right;left;reflexivity)))
    as (m1 & CX2 & X1M1 & X2M1 & FX1M1 & FX2M1 & F1 & R1).
  assert (Free1:Forall (fun bi=>Mem.range_perm m1 bi 0 40 Cur Freeable) [bx1;bx2;bx3;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F1|exact FX1M1|exact FX2M1|exact Free]).
  pose proof Free1 as All1;rewrite Forall_forall in All1.
  assert (Y1M1:fe_at m1 by1 0 (words5 y1)) by
    (eapply swu_two_keep_field;[| |exact Y1|exact F1];congruence).
  assert (Y2M1:fe_at m1 by2 0 (words5 y2)) by
    (eapply swu_two_keep_field;[| |exact Y2|exact F1];congruence).
  assert (X3M1:fe_at m1 bx3 0 (words5 x3)) by
    (eapply swu_two_keep_field;[| |exact X3|exact F1];congruence).
  assert (Y3M1:fe_at m1 by3 0 (words5 y3)) by
    (eapply swu_two_keep_field;[| |exact Y3|exact F1];congruence).
  destruct (eval_field_cmov (swu_select_bool false alpha beta) y1 y2 m1 by1 by2 Y12 Y1M1 Y2M1
    (All1 by1 ltac:(do 3 right;left;reflexivity)) (All1 by2 ltac:(do 4 right;left;reflexivity)))
    as (m2 & CY2 & Y1M2 & Y2M2 & FY1M2 & FY2M2 & F2 & R2).
  assert (Free2:Forall (fun bi=>Mem.range_perm m2 bi 0 40 Cur Freeable) [bx1;bx2;bx3;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F2|exact FY1M2|exact FY2M2|exact Free1]).
  pose proof Free2 as All2;rewrite Forall_forall in All2.
  assert (X1M2:fe_at m2 bx1 0 (words5 (if swu_select_bool false alpha beta then x2 else x1))) by
    (eapply swu_two_keep_field;[| |exact X1M1|exact F2];congruence).
  assert (X3M2:fe_at m2 bx3 0 (words5 x3)) by
    (eapply swu_two_keep_field;[| |exact X3M1|exact F2];congruence).
  assert (Y3M2:fe_at m2 by3 0 (words5 y3)) by
    (eapply swu_two_keep_field;[| |exact Y3M1|exact F2];congruence).
  destruct (eval_field_cmov (swu_select_bool true alpha beta)
    (if swu_select_bool false alpha beta then x2 else x1) x3 m2 bx1 bx3 X13 X1M2 X3M2
    (All2 bx1 ltac:(left;reflexivity)) (All2 bx3 ltac:(do 2 right;left;reflexivity)))
    as (m3 & CX3 & X1M3 & X3M3 & FX1M3 & FX3M3 & F3 & R3).
  rewrite swu_selected_words_compose in X1M3.
  assert (Free3:Forall (fun bi=>Mem.range_perm m3 bi 0 40 Cur Freeable) [bx1;bx2;bx3;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F3|exact FX1M3|exact FX3M3|exact Free2]).
  pose proof Free3 as All3;rewrite Forall_forall in All3.
  assert (Y1M3:fe_at m3 by1 0 (words5 (if swu_select_bool false alpha beta then y2 else y1))) by
    (eapply swu_two_keep_field;[| |exact Y1M2|exact F3];congruence).
  assert (Y3M3:fe_at m3 by3 0 (words5 y3)) by
    (eapply swu_two_keep_field;[| |exact Y3M2|exact F3];congruence).
  destruct (eval_field_cmov (swu_select_bool true alpha beta)
    (if swu_select_bool false alpha beta then y2 else y1) y3 m3 by1 by3 Y13 Y1M3 Y3M3
    (All3 by1 ltac:(do 3 right;left;reflexivity)) (All3 by3 ltac:(do 5 right;left;reflexivity)))
    as (mf & CY3 & Y1F & Y3F & FY1F & FY3F & F4 & R4).
  rewrite swu_selected_words_compose in Y1F.
  assert (FreeF:Forall (fun bi=>Mem.range_perm mf bi 0 40 Cur Freeable) [bx1;bx2;bx3;by1;by2;by3]) by
    (eapply swu_two_keep_free;[exact F4|exact FY1F|exact FY3F|exact Free3]).
  assert (X1F:fe_at mf bx1 0 (words5 (swu_selected_words alpha beta x1 x2 x3))) by
    (eapply swu_two_keep_field;[| |exact X1M3|exact F4];congruence).
  exists mf;split.
  - unfold swu_select_prefix,swu_select_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);
      [eapply (exec_swu_select_call false false alpha beta);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);
      [eapply (exec_swu_select_call false true alpha beta);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);
      [eapply (exec_swu_select_call true false alpha beta);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le);
      [eapply (exec_swu_select_call true true alpha beta);eassumption|apply exec_Sskip].
  - split;[exact X1F|];split;[exact Y1F|];split;[exact FreeF|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact F1|];intros bi pos Outside Valid;
          split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto.
      * eapply lframe_trans with (m2:=m2).
        { eapply lframe_implies;[exact F2|];intros bi pos Outside Valid;
            split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto. }
        eapply lframe_trans with (m2:=m3).
        { eapply lframe_implies;[exact F3|];intros bi pos Outside Valid;
            split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto. }
        eapply lframe_implies;[exact F4|];intros bi pos Outside Valid;
          split;intro Same;apply Outside;subst;clear -Outside;cbn;tauto.
    + eapply preserved_trans;[exact R1|];eapply preserved_trans;[exact R2|];
        eapply preserved_trans;[exact R3|exact R4].
Qed.

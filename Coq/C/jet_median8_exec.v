(** Actual byte median: promotions, the complete comparison/cast tree and call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8_exec.
Require Import C.jet_add8_word C.jet_word_repr C.jet_binary8_exec C.jet_median_spec C.jet_median_control.
Require Import C.jet_order_spec C.jet_order8_exec C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition median8 := f_simplicity_median_8.
Definition median8_raw r t u :=
  median_decision (order8_bit OLt r t) (order8_bit OLt t u) (order8_bit OLt u r)
    (order8_bit OLt r u) (order8_bit OLt u t) (Int.zero_ext 8 r) (Int.zero_ext 8 t) (Int.zero_ext 8 u).
Definition median8_payload r t u := Int.zero_ext 8 (median8_raw r t u).
Definition le_median8_x env bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (median8) bd dofs bs sofs)).
Definition le_median8_y env bd dofs bs sofs r t :=
  PTree.set _y (Vint (Int.zero_ext 8 t)) (PTree.set _t'2 (Vint t) (le_median8_x env bd dofs bs sofs r)).
Definition le_median8_z env bd dofs bs sofs r t u :=
  PTree.set _z (Vint (Int.zero_ext 8 u)) (PTree.set _t'3 (Vint u) (le_median8_y env bd dofs bs sofs r t)).

Lemma median8_body : (median8).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence
          (Ssequence (binary8_read _t'3) (Sset _z (Ecast (Etempvar _t'3 tuchar) tuchar)))
          (Ssequence
            (Ssequence (median_choose tuchar tint)
              (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'4 tint)))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. reflexivity. Qed.

Lemma eval_median8_cmp e le m a b r t :
  le!a = Some (Vint (Int.zero_ext 8 r)) -> le!b = Some (Vint (Int.zero_ext 8 t)) ->
  eval_expr ge0 e le m (median_cmp tuchar a b) (Vint (bit_int (order8_bit OLt r t))).
Proof.
  intros HX HY. eapply eval_Ebinop; [apply eval_Etempvar; exact HX|apply eval_Etempvar; exact HY|].
  change (Some (Val.of_bool (Int.lt (Int.zero_ext 8 r) (Int.zero_ext 8 t))) =
    Some (Vint (bit_int (Int.lt (Int.zero_ext 8 r) (Int.zero_ext 8 t))))).
  destruct (Int.lt (Int.zero_ext 8 r) (Int.zero_ext 8 t)); reflexivity.
Qed.
Lemma exec_median8_choose e le m r t u :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  le!_z = Some (Vint (Int.zero_ext 8 u)) ->
  Clight2.exec_stmt ge0 e le m (median_choose tuchar tint) E0
    (PTree.set _t'4 (Vint (median8_raw r t u)) le) m Out_normal.
Proof.
  intros HX HY HZ.
  assert (Hvalue : Vint (median8_raw r t u) =
    median_decision (order8_bit OLt r t) (order8_bit OLt t u) (order8_bit OLt u r)
      (order8_bit OLt r u) (order8_bit OLt u t)
      (Vint (Int.zero_ext 8 r)) (Vint (Int.zero_ext 8 t)) (Vint (Int.zero_ext 8 u))).
  { unfold median8_raw, median_decision.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. }
  rewrite Hvalue. apply exec_median_choose.
  - apply eval_median8_cmp; assumption.
  - apply eval_median8_cmp; assumption.
  - apply eval_median8_cmp; assumption.
  - apply eval_median8_cmp; assumption.
  - apply eval_median8_cmp; assumption.
  - eapply eval_Ecast; [apply eval_Etempvar; exact HX|reflexivity].
  - eapply eval_Ecast; [apply eval_Etempvar; exact HY|reflexivity].
  - eapply eval_Ecast; [apply eval_Etempvar; exact HZ|reflexivity].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma eval_median8_composes env m ma mc mr mr2 mr3 me mf bl bd dbase bs sbase bytes r t u :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr3 (Vint u) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (median8_payload r t u)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (median8))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (median8) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'4 (Vint (median8_raw r t u))
      (le_median8_z env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _t'4; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite median8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_median8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_median8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_binary8_read. exact Hread3.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
             (le1 := PTree.set _t'4 (Vint (median8_raw r t u))
               (le_median8_z env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u)).
           { apply exec_median8_choose.
             - unfold le_median8_z, le_median8_y, le_median8_x.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_median8_z, le_median8_y.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_median8_z. rewrite PTree.gss. reflexivity. }
           eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (median8_raw r t u)) (v := Vint (median8_payload r t u)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_median8_z, le_median8_y, le_median8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

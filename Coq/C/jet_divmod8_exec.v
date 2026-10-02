(** Complete actual div_mod_8: two reads, both guarded operations, ordered
    quotient/remainder byte writes, return and freeing the local source frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_wide.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8 C.jet_increment8_exec.
Require Import C.jet_binary8_exec C.jet_division8_expr C.jet_division_value C.jet_divmod_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition le_divmod8_x env bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env f_simplicity_div_mod_8 bd dofs bs sofs)).
Definition le_divmod8_y env bd dofs bs sofs r t :=
  PTree.set _y (Vint (Int.zero_ext 8 t)) (PTree.set _t'2 (Vint t) (le_divmod8_x env bd dofs bs sofs r)).

Lemma divmod8_body : f_simplicity_div_mod_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence
          (Ssequence (divmod8_choose _t'3 Datatypes.false)
            (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'3 tint)))
          (Ssequence
            (Ssequence (divmod8_choose _t'4 Datatypes.true)
              (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'4 tint)))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. reflexivity. Qed.

Lemma eval_divmod8_composes env m ma mc mr mr2 mq me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (division8_payload Datatypes.false r t)] E0 mq Vundef ->
  Clight2.eval_funcall ge0 mq (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (division8_payload Datatypes.true r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_div_mod_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 HwriteQ HwriteR HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_div_mod_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'4 (Vint (division8_raw Datatypes.true r t))
      (PTree.set _t'3 (Vint (division8_raw Datatypes.false r t))
        (le_divmod8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'4; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|[H2|[H2|H2]]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite divmod8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_divmod8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mq)
          (le1 := PTree.set _t'3 (Vint (division8_raw Datatypes.false r t))
            (le_divmod8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
             (le1 := PTree.set _t'3 (Vint (division8_raw Datatypes.false r t))
               (le_divmod8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)).
           { apply exec_divmod8_choose.
             - unfold le_divmod8_y, le_divmod8_x.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_divmod8_y. rewrite PTree.gss. reflexivity. }
           eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (division8_raw Datatypes.false r t))
             (v := Vint (division8_payload Datatypes.false r t)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_divmod8_y, le_divmod8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact HwriteQ.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mq)
                (le1 := PTree.set _t'4 (Vint (division8_raw Datatypes.true r t))
                  (PTree.set _t'3 (Vint (division8_raw Datatypes.false r t))
                    (le_divmod8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t))).
              { apply exec_divmod8_choose.
                - unfold le_divmod8_y, le_divmod8_x.
                  rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
                - unfold le_divmod8_y. rewrite PTree.gso by discriminate. rewrite PTree.gss. reflexivity. }
              eapply call_frame_writer_cast with (f := f_simplicity_write8)
                (vraw := Vint (division8_raw Datatypes.true r t))
                (v := Vint (division8_payload Datatypes.true r t)) (vret := Vundef).
              ** reflexivity.
              ** unfold le_divmod8_y, le_divmod8_x, le_arith8_layout.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** reflexivity.
              ** apply symbol_write8.
              ** apply funct_write8.
              ** apply eval_Etempvar. rewrite PTree.gss. reflexivity.
              ** reflexivity.
              ** exact HwriteR.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

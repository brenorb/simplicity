(** Complete actual divide_8/modulo_8 calls through internal reader/writer
    contracts. Canonical equivalence still requires a separate program bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_wide.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8 C.jet_increment8_exec.
Require Import C.jet_add8_word C.jet_word_repr.
Require Import C.jet_binary8_exec C.jet_division8_expr C.jet_division_value.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition division8 (remainder : bool) := if remainder then f_simplicity_modulo_8 else f_simplicity_divide_8.
Definition le_division8_x env remainder bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (division8 remainder) bd dofs bs sofs)).
Definition le_division8_y env remainder bd dofs bs sofs r t :=
  PTree.set _y (Vint (Int.zero_ext 8 t)) (PTree.set _t'2 (Vint t) (le_division8_x env remainder bd dofs bs sofs r)).

Lemma division8_body remainder : (division8 remainder).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence
          (Ssequence (division8_choose remainder)
            (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'3 tint)))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct remainder; reflexivity. Qed.

Lemma eval_division8_composes env remainder m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (division8_payload remainder r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (division8 remainder))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (division8 remainder) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'3 (Vint (division8_raw remainder r t))
      (le_division8_y env remainder bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct remainder; reflexivity|destruct remainder; reflexivity| |exact HA].
    destruct remainder; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite division8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct remainder; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_division8_x env remainder bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
             (le1 := PTree.set _t'3 (Vint (division8_raw remainder r t))
               (le_division8_y env remainder bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)).
           { apply exec_division8_choose.
             - unfold le_division8_y, le_division8_x.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_division8_y. rewrite PTree.gss. reflexivity. }
           eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (division8_raw remainder r t)) (v := Vint (division8_payload remainder r t)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_division8_y, le_division8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct remainder; cbn; split; solve [discriminate|reflexivity].
  - destruct remainder; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

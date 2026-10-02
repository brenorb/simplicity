(** Actual divide/modulo at 16/32/64 bits: two reads, guarded arithmetic,
    one write and cleanup. Canonical equivalence is a separate obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_division_value C.jet_division_wide_expr C.jet_binary_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_division (remainder : bool) s := match remainder, s with
  | false, W16 => f_simplicity_divide_16 | false, W32 => f_simplicity_divide_32 | false, W64 => f_simplicity_divide_64
  | true, W16 => f_simplicity_modulo_16 | true, W32 => f_simplicity_modulo_32 | true, W64 => f_simplicity_modulo_64 end.
Definition le_wide_division_x env remainder s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_division remainder s) bd dofs bs sofs)).
Definition le_wide_division_y env remainder s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_division_x env remainder s bd dofs bs sofs r)).

Lemma wide_division_body remainder s : (wide_division remainder s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (division_wide_choose remainder)
            (frame_writer_call (wide_writer_id s) tulong tvoid (Etempvar _t'3 tulong)))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct remainder, s; reflexivity. Qed.

Lemma eval_wide_division_composes env remainder s m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (division_wide_raw remainder r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_division remainder s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_division remainder s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'3 (Vlong (division_wide_raw remainder r t))
      (le_wide_division_y env remainder s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct remainder, s; reflexivity|destruct remainder, s; reflexivity| |exact HA].
    destruct remainder, s; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_division_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct remainder, s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_division_x env remainder s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
             (le1 := PTree.set _t'3 (Vlong (division_wide_raw remainder r t))
               (le_wide_division_y env remainder s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)).
           { apply exec_division_wide_choose.
             - unfold le_wide_division_y, le_wide_division_x.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_wide_division_y. rewrite PTree.gss. reflexivity. }
           eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := Vlong (division_wide_raw remainder r t)) (v := Vlong (division_wide_raw remainder r t)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_division_y, le_wide_division_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct remainder, s; cbn; split; solve [discriminate|reflexivity].
  - destruct remainder, s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

(** Actual and/or/xor bodies at 16/32/64 bits: two reads, one write, cleanup. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_binary k s := match k, s with
  | BAnd, W16 => f_simplicity_and_16 | BAnd, W32 => f_simplicity_and_32 | BAnd, W64 => f_simplicity_and_64
  | BOr, W16 => f_simplicity_or_16 | BOr, W32 => f_simplicity_or_32 | BOr, W64 => f_simplicity_or_64
  | BXor, W16 => f_simplicity_xor_16 | BXor, W32 => f_simplicity_xor_32 | BXor, W64 => f_simplicity_xor_64
  end.
Definition binary_clight_op k := match k with BAnd => Oand | BOr => Oor | BXor => Oxor end.
Definition wide_binary_expr k := Ebinop (binary_clight_op k) (Etempvar _x tulong) (Etempvar _y tulong) tulong.
Definition wide_binary_read s result := Scall (Some result)
  (Evar (wide_reader_id s) (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
  [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition le_wide_binary_x env k s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_binary k s) bd dofs bs sofs)).
Definition le_wide_binary_y env k s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_binary_x env k s bd dofs bs sofs r)).

Lemma wide_binary_body k s : (wide_binary k s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid (wide_binary_expr k))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k, s; reflexivity. Qed.

Lemma call_wide_binary_read s result le m mr bl r :
  Clight2.eval_funcall ge0 m (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (wide_binary_read s result)
    E0 (PTree.set result (Vlong r) le) mr Out_normal.
Proof.
  intros Hread. eapply exec_Scall with (vf := Vptr (jet_symbol_block (wide_reader_id s)) Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal (wide_reader s)) (vres := Vlong r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [destruct s; reflexivity|apply wide_reader_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof. eapply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply wide_reader_funct.
  - destruct s; reflexivity.
  - exact Hread.
Qed.

Lemma eval_wide_binary_expr k e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m (wide_binary_expr k) (Vlong (binary_int64 k r t)).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
  - eapply eval_Etempvar; exact HX.
  - eapply eval_Etempvar; exact HY.
  - destruct k; reflexivity.
Qed.

Lemma eval_wide_binary_composes env k s m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (binary_int64 k r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_binary k s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_binary k s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_binary_y env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k, s; reflexivity|destruct k, s; reflexivity| |exact HA].
    destruct k, s; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_binary_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k, s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_binary_x env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := Vlong (binary_int64 k r t)) (v := Vlong (binary_int64 k r t)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_binary_y, le_wide_binary_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_wide_binary_expr.
              ** unfold le_wide_binary_y, le_wide_binary_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_wide_binary_y. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k, s; cbn; split; solve [discriminate|reflexivity].
  - destruct k, s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

(** Actual median bodies at 16/32/64 bits: three reads, full decision tree, one write. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_wide_exec C.jet_median_spec C.jet_median_control C.jet_order_spec C.jet_order_wide_exec.
Require Import C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_median s := match s with
  | W16 => f_simplicity_median_16 | W32 => f_simplicity_median_32 | W64 => f_simplicity_median_64 end.
Definition median_int64 r t u := median_select (fun a b => wide_order_bit OLt a b) r t u.
Definition le_wide_median_x env s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_median s) bd dofs bs sofs)).
Definition le_wide_median_y env s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_median_x env s bd dofs bs sofs r)).
Definition le_wide_median_z env s bd dofs bs sofs r t u :=
  PTree.set _z (Vlong u) (PTree.set _t'3 (Vlong u) (le_wide_median_y env s bd dofs bs sofs r t)).

Lemma wide_median_body s : (wide_median s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (wide_binary_read s _t'3) (Sset _z (Etempvar _t'3 tulong)))
          (Ssequence
            (Ssequence (median_choose tulong tulong)
              (frame_writer_call (wide_writer_id s) tulong tvoid (Etempvar _t'4 tulong)))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_median_long_cmp e le m a b r t :
  le!a = Some (Vlong r) -> le!b = Some (Vlong t) ->
  eval_expr ge0 e le m (median_cmp tulong a b) (Vint (bit_int (wide_order_bit OLt r t))).
Proof.
  intros HX HY. eapply eval_Ebinop; [apply eval_Etempvar; exact HX|apply eval_Etempvar; exact HY|].
  change (Some (Val.of_bool (Int64.ltu r t)) = Some (Vint (bit_int (Int64.ltu r t)))).
  destruct (Int64.ltu r t); reflexivity.
Qed.
Lemma exec_wide_median_choose e le m r t u :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) -> le!_z = Some (Vlong u) ->
  Clight2.exec_stmt ge0 e le m (median_choose tulong tulong) E0
    (PTree.set _t'4 (Vlong (median_int64 r t u)) le) m Out_normal.
Proof.
  intros HX HY HZ.
  assert (Hvalue : Vlong (median_int64 r t u) =
    median_decision (wide_order_bit OLt r t) (wide_order_bit OLt t u) (wide_order_bit OLt u r)
      (wide_order_bit OLt r u) (wide_order_bit OLt u t) (Vlong r) (Vlong t) (Vlong u)).
  { unfold median_int64, median_select, median_decision.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. }
  rewrite Hvalue. apply exec_median_choose.
  - apply eval_median_long_cmp; assumption.
  - apply eval_median_long_cmp; assumption.
  - apply eval_median_long_cmp; assumption.
  - apply eval_median_long_cmp; assumption.
  - apply eval_median_long_cmp; assumption.
  - eapply eval_Ecast; [apply eval_Etempvar; exact HX|reflexivity].
  - eapply eval_Ecast; [apply eval_Etempvar; exact HY|reflexivity].
  - eapply eval_Ecast; [apply eval_Etempvar; exact HZ|reflexivity].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma eval_wide_median_composes env s m ma mc mr mr2 mr3 me mf bl bd dbase bs sbase bytes r t u :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong u) ->
  Clight2.eval_funcall ge0 mr3 (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (median_int64 r t u)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_median s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_median s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'4 (Vlong (median_int64 r t u))
      (le_wide_median_z env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _t'4; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_median_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_median_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_wide_median_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_wide_binary_read. exact Hread3.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
             (le1 := PTree.set _t'4 (Vlong (median_int64 r t u))
               (le_wide_median_z env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u)).
           { apply exec_wide_median_choose.
             - unfold le_wide_median_z, le_wide_median_y, le_wide_median_x.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_wide_median_z, le_wide_median_y.
               rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
             - unfold le_wide_median_z. rewrite PTree.gss. reflexivity. }
           eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := Vlong (median_int64 r t u)) (v := Vlong (median_int64 r t u)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_median_z, le_wide_median_y, le_wide_median_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

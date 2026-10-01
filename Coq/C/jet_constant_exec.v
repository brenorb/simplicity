(** Function-entry, cast, actual body, return conversion and local cleanup
    for the ten generated low/high jets. The writer is composed separately. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_constant.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma constant_body s high : (constant_jet s high).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence (frame_writer_call (constant_writer_id s) (constant_arg_type s)
      (constant_return_type s) (constant_expr s high))
      (Sreturn (Some (Econst_int Int.one tint)))).
Proof. destruct s, high; reflexivity. Qed.

Lemma constant_expr_eval s high e le m :
  eval_expr ge0 e le m (constant_expr s high) (constant_raw s high).
Proof. destruct s, high; constructor. Qed.

Lemma eval_constant_composes env s high m ma mc me mf bl bd dbase bs sbase bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal (constant_writer s))
    [Vptr bd (Ptrofs.repr dbase); constant_value s high] E0 me (constant_return s high) ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal (constant_jet s high))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HSbase HSAlign HD HA HB SC HW HF.
  set (le := le_arith8_layout env (constant_jet s high) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl) (le1 := le) (le2 := le) (m1 := ma) (m2 := me)
      (out := Out_return (Some (Vint Int.one, tint))).
  - apply entry_frame_jet; try (destruct s, high; reflexivity).
    + destruct s, high; change (list_disjoint [_dst; _src; _env] []);
        intros i j HI HJ; contradiction.
    + exact HA.
  - rewrite constant_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s, high; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply call_frame_writer_cast with (f := constant_writer s)
          (vraw := constant_raw s high) (v := constant_value s high).
        -- destruct s, high; reflexivity.
        -- destruct s, high; reflexivity.
        -- destruct s; reflexivity.
        -- apply constant_writer_symbol.
        -- apply constant_writer_funct.
        -- apply constant_expr_eval.
        -- apply constant_cast.
        -- exact HW.
      * apply exec_Sreturn_some; apply eval_Econst_int.
  - destruct s, high; cbn; split; solve [discriminate | reflexivity].
  - destruct s, high; change (Mem.free_list me [(bl, 0, 16)] = Some mf);
      cbn; rewrite HF; reflexivity.
Qed.

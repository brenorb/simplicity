(** Function-boundary composition for the actual one_16/one_32/one_64 bodies. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_wide C.jet_frame_layout C.jet_arith8_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma wide_one_body s : (wide_one s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid (Econst_int Int.one tint))
      (Sreturn (Some (Econst_int Int.one tint)))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_one_wide_layout_composes s m ma mc me mf bl bd dbase bs sbase bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong Int64.one] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_one s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vundef] E0 mf (Vint Int.one).
Proof.
  intros HSbase HSAlign HD HA HB SC HW HF.
  set (le := le_arith8_layout (wide_one s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl) (le1 := le) (le2 := le) (m1 := ma) (m2 := me)
      (out := Out_return (Some (Vint Int.one, tint))).
  - apply entry_frame_jet; try (destruct s; reflexivity).
    + destruct s; change (list_disjoint [_dst; _src; _env] []); intros i j HI HJ; contradiction.
    + exact HA.
  - rewrite wide_one_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply call_frame_writer_cast with (f := wide_writer s)
          (vraw := Vint Int.one) (v := Vlong Int64.one).
        -- destruct s; reflexivity.
        -- destruct s; reflexivity.
        -- destruct s; reflexivity.
        -- apply wide_writer_symbol.
        -- apply wide_writer_funct.
        -- apply eval_Econst_int.
        -- reflexivity.
        -- exact HW.
      * apply exec_Sreturn_some; apply eval_Econst_int.
  - destruct s; cbn; split; [discriminate|reflexivity|discriminate|reflexivity|discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

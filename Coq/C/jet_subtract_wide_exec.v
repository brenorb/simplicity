(** Actual subtract_16/32/64 calls: two reads, borrow bit, payload, cleanup. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_wide_exec C.jet_readBit_layout C.jet_increment8_exec C.jet_subtract_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_subtract s := match s with W16 => f_simplicity_subtract_16
  | W32 => f_simplicity_subtract_32 | W64 => f_simplicity_subtract_64 end.
Definition wide_subtract_borrow_expr := Ebinop Olt (Etempvar _x tulong) (Etempvar _y tulong) tint.
Definition wide_subtract_payload_expr := Ecast
  (Ebinop Osub (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong)
    (Etempvar _y tulong) tulong) tulong.
Definition le_wide_subtract_x env s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_subtract s) bd dofs bs sofs)).
Definition le_wide_subtract_y env s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_subtract_x env s bd dofs bs sofs r)).

Lemma wide_subtract_body s : (wide_subtract s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence (frame_writer_call _writeBit tbool tbool wide_subtract_borrow_expr)
          (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid wide_subtract_payload_expr)
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_wide_subtract_borrow_expr e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m wide_subtract_borrow_expr (Vint (bit_int (wide_subtract_borrow r t))).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
  - apply eval_Etempvar. exact HX.
  - apply eval_Etempvar. exact HY.
  - change (Some (Val.of_bool (wide_subtract_borrow r t)) = Some (Vint (bit_int (wide_subtract_borrow r t)))).
    destruct (wide_subtract_borrow r t); reflexivity.
Qed.
Lemma eval_wide_subtract_payload_expr e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m wide_subtract_payload_expr (Vlong (wide_subtract_payload r t)).
Proof.
  intros HX HY. eapply eval_Ecast with (v1 := Vlong (wide_subtract_payload r t)).
  - eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
      * apply eval_Econst_int.
      * apply eval_Etempvar. exact HX.
      * change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
        rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
    + apply eval_Etempvar. exact HY.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eval_wide_subtract_composes env s m ma mc mr mr2 mb me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_subtract_borrow r t))]
    E0 mb (Vint (bit_int (wide_subtract_borrow r t))) ->
  Clight2.eval_funcall ge0 mb (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (wide_subtract_payload r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_subtract s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_subtract s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_subtract_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_subtract_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_subtract_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_wide_subtract_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        assert (HX : (le_wide_subtract_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)!_x = Some (Vlong r)).
        { unfold le_wide_subtract_y. rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HY : (le_wide_subtract_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)!_y = Some (Vlong t))
          by (apply PTree.gss).
        assert (HDst : (le_wide_subtract_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_wide_subtract_y, le_wide_subtract_x, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        { eapply call_frame_writer_cast with (f := f_writeBit)
            (vraw := Vint (bit_int (wide_subtract_borrow r t)))
            (v := Vint (bit_int (wide_subtract_borrow r t)))
            (vret := Vint (bit_int (wide_subtract_borrow r t))).
          - reflexivity.
          - exact HDst.
          - reflexivity.
          - apply symbol_writeBit.
          - apply funct_writeBit.
          - apply eval_wide_subtract_borrow_expr; assumption.
          - destruct (wide_subtract_borrow r t); reflexivity.
          - exact Hbit. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        { eapply call_frame_writer with (f := wide_writer s) (v := Vlong (wide_subtract_payload r t)) (vret := Vundef).
          - destruct s; reflexivity.
          - exact HDst.
          - destruct s; reflexivity.
          - apply wide_writer_symbol.
          - apply wide_writer_funct.
          - apply eval_wide_subtract_payload_expr; assumption.
          - reflexivity.
          - exact Hwrite. }
        apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

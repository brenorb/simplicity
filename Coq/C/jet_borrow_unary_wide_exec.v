(** Actual wide negate/decrement bodies: one read, borrow and payload writes. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_wide_exec C.jet_readBit_layout C.jet_increment8_exec C.jet_borrow_unary_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_borrow_unary k s := match k, s with
  | UNegate, W16 => f_simplicity_negate_16 | UNegate, W32 => f_simplicity_negate_32
  | UNegate, W64 => f_simplicity_negate_64 | UDecrement, W16 => f_simplicity_decrement_16
  | UDecrement, W32 => f_simplicity_decrement_32 | UDecrement, W64 => f_simplicity_decrement_64 end.
Definition wide_unary_borrow_expr k := match k with
  | UNegate => Ebinop One (Etempvar _x tulong) (Econst_int Int.zero tint) tint
  | UDecrement => Ebinop Olt (Etempvar _x tulong) (Econst_int Int.one tint) tint end.
Definition wide_unary_mul_expr := Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong.
Definition wide_unary_payload_expr k := Ecast (match k with
  | UNegate => Eunop Oneg wide_unary_mul_expr tulong
  | UDecrement => Ebinop Osub wide_unary_mul_expr (Econst_int Int.one tint) tulong end) tulong.
Definition le_wide_borrow_unary_x env k s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_borrow_unary k s) bd dofs bs sofs)).

Lemma wide_borrow_unary_body k s : (wide_borrow_unary k s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence (frame_writer_call _writeBit tbool tbool (wide_unary_borrow_expr k))
        (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid (wide_unary_payload_expr k))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k, s; reflexivity. Qed.
Lemma eval_wide_unary_borrow_expr k e le m r :
  le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m (wide_unary_borrow_expr k) (Vint (bit_int (wide_unary_borrow k r))).
Proof.
  intros HX. destruct k; eapply eval_Ebinop with (v1 := Vlong r).
  all: try solve [apply eval_Etempvar; exact HX|apply eval_Econst_int].
  all: lazymatch goal with |- _ = Some (Vint (bit_int ?b)) =>
    change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity end.
Qed.
Lemma eval_wide_unary_mul_expr e le m r :
  le!_x = Some (Vlong r) -> eval_expr ge0 e le m wide_unary_mul_expr (Vlong r).
Proof.
  intros HX. eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
  - apply eval_Econst_int.
  - apply eval_Etempvar. exact HX.
  - change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
    rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
Qed.
Lemma eval_wide_unary_payload_expr k e le m r :
  le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m (wide_unary_payload_expr k) (Vlong (wide_unary_payload k r)).
Proof.
  intros HX. destruct k; eapply eval_Ecast with (v1 := Vlong (wide_unary_payload _ r)); [|reflexivity| |reflexivity].
  - eapply eval_Eunop with (v1 := Vlong r); [apply eval_wide_unary_mul_expr; exact HX|reflexivity].
  - eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint Int.one).
    + apply eval_wide_unary_mul_expr. exact HX.
    + apply eval_Econst_int.
    + reflexivity.
Qed.

Lemma eval_wide_borrow_unary_composes env k s m ma mc mr mb me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_unary_borrow k r))]
    E0 mb (Vint (bit_int (wide_unary_borrow k r))) ->
  Clight2.eval_funcall ge0 mb (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (wide_unary_payload k r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_borrow_unary k s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_borrow_unary k s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_borrow_unary_x env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k, s; reflexivity|destruct k, s; reflexivity| |exact HA].
    destruct k, s; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_borrow_unary_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k, s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        - apply call_wide_binary_read. exact Hread.
        - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
      assert (HX : (le_wide_borrow_unary_x env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)!_x = Some (Vlong r))
        by (apply PTree.gss).
      assert (HDst : (le_wide_borrow_unary_x env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)!_dst =
        Some (Vptr bd (Ptrofs.repr dbase))).
      { unfold le_wide_borrow_unary_x, le_arith8_layout. rewrite !PTree.gso by discriminate. apply PTree.gss. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
      { eapply call_frame_writer_cast with (f := f_writeBit)
          (vraw := Vint (bit_int (wide_unary_borrow k r)))
          (v := Vint (bit_int (wide_unary_borrow k r))) (vret := Vint (bit_int (wide_unary_borrow k r))).
        - reflexivity.
        - exact HDst.
        - reflexivity.
        - apply symbol_writeBit.
        - apply funct_writeBit.
        - apply eval_wide_unary_borrow_expr. exact HX.
        - destruct k, (wide_unary_borrow _ r); reflexivity.
        - exact Hbit. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
      { eapply call_frame_writer with (f := wide_writer s) (v := Vlong (wide_unary_payload k r)) (vret := Vundef).
        - destruct s; reflexivity.
        - exact HDst.
        - destruct s; reflexivity.
        - apply wide_writer_symbol.
        - apply wide_writer_funct.
        - apply eval_wide_unary_payload_expr. exact HX.
        - destruct k; reflexivity.
        - exact Hwrite. }
      apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k, s; cbn; split; solve [discriminate|reflexivity].
  - destruct k, s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

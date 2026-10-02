(** Actual byte negate/decrement bodies: one read, borrow and payload writes. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary8_exec C.jet_readBit_layout C.jet_increment8_exec C.jet_add8 C.jet_borrow_unary_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition borrow_unary8 k := match k with UNegate => f_simplicity_negate_8 | UDecrement => f_simplicity_decrement_8 end.
Definition unary8_borrow_expr k := match k with
  | UNegate => Ebinop One (Etempvar _x tuchar) (Econst_int Int.zero tint) tint
  | UDecrement => Ebinop Olt (Etempvar _x tuchar) (Econst_int Int.one tint) tint end.
Definition unary8_mul_expr := Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint.
Definition unary8_payload_expr k := Ecast (match k with
  | UNegate => Eunop Oneg unary8_mul_expr tuint
  | UDecrement => Ebinop Osub unary8_mul_expr (Econst_int Int.one tint) tuint end) tuchar.
Definition le_borrow_unary8_x env k bd dofs bs sofs r :=
  PTree.set _x (Vint (add8_u r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (borrow_unary8 k) bd dofs bs sofs)).

Lemma borrow_unary8_body k : (borrow_unary8 k).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence (frame_writer_call _writeBit tbool tbool (unary8_borrow_expr k))
        (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid (unary8_payload_expr k))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k; reflexivity. Qed.
Lemma eval_unary8_borrow_expr k e le m r :
  le!_x = Some (Vint (add8_u r)) ->
  eval_expr ge0 e le m (unary8_borrow_expr k) (Vint (bit_int (unary8_borrow k r))).
Proof.
  intros HX. destruct k; eapply eval_Ebinop with (v1 := Vint (add8_u r)).
  all: try solve [apply eval_Etempvar; exact HX|apply eval_Econst_int].
  all: lazymatch goal with |- _ = Some (Vint (bit_int ?b)) =>
    change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity end.
Qed.
Lemma eval_unary8_mul_expr e le m r :
  le!_x = Some (Vint (add8_u r)) ->
  eval_expr ge0 e le m unary8_mul_expr (Vint (Int.mul Int.one (add8_u r))).
Proof.
  intros HX. eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint (add8_u r)).
  - apply eval_Econst_int.
  - apply eval_Etempvar. exact HX.
  - reflexivity.
Qed.
Lemma eval_unary8_payload_expr k e le m r :
  le!_x = Some (Vint (add8_u r)) ->
  eval_expr ge0 e le m (unary8_payload_expr k) (Vint (unary8_payload k r)).
Proof.
  intros HX. destruct k.
  - eapply eval_Ecast with (v1 := Vint (Int.neg (Int.mul Int.one (add8_u r)))).
    + eapply eval_Eunop with (v1 := Vint (Int.mul Int.one (add8_u r)));
        [apply eval_unary8_mul_expr; exact HX|reflexivity].
    + reflexivity.
  - eapply eval_Ecast with (v1 := Vint (Int.sub (Int.mul Int.one (add8_u r)) Int.one)).
    + eapply eval_Ebinop with (v1 := Vint (Int.mul Int.one (add8_u r))) (v2 := Vint Int.one).
      * apply eval_unary8_mul_expr. exact HX.
      * apply eval_Econst_int.
      * reflexivity.
    + reflexivity.
Qed.

Lemma eval_borrow_unary8_composes env k m ma mc mr mb me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (unary8_borrow k r))]
    E0 mb (Vint (bit_int (unary8_borrow k r))) ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (unary8_payload k r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (borrow_unary8 k))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (borrow_unary8 k) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_borrow_unary8_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k; reflexivity|destruct k; reflexivity| |exact HA].
    destruct k; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite borrow_unary8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        - apply call_binary8_read. exact Hread.
        - apply exec_set. eapply eval_Ecast.
          + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
          + reflexivity. }
      assert (HX : (le_borrow_unary8_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)!_x = Some (Vint (add8_u r)))
        by (apply PTree.gss).
      assert (HDst : (le_borrow_unary8_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)!_dst =
        Some (Vptr bd (Ptrofs.repr dbase))).
      { unfold le_borrow_unary8_x, le_arith8_layout. rewrite !PTree.gso by discriminate. apply PTree.gss. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
      { eapply call_frame_writer_cast with (f := f_writeBit)
          (vraw := Vint (bit_int (unary8_borrow k r)))
          (v := Vint (bit_int (unary8_borrow k r))) (vret := Vint (bit_int (unary8_borrow k r))).
        - reflexivity.
        - exact HDst.
        - reflexivity.
        - apply symbol_writeBit.
        - apply funct_writeBit.
        - apply eval_unary8_borrow_expr. exact HX.
        - destruct k, (unary8_borrow _ r); reflexivity.
        - exact Hbit. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
      { eapply call_frame_writer with (f := f_simplicity_write8) (v := Vint (unary8_payload k r)) (vret := Vundef).
        - reflexivity.
        - exact HDst.
        - reflexivity.
        - apply symbol_write8.
        - apply funct_write8.
        - apply eval_unary8_payload_expr. exact HX.
        - destruct k; unfold unary8_payload;
            lazymatch goal with |- _ = Some (Vint (Int.zero_ext 8 ?v)) =>
              change (Some (Vint (Int.zero_ext 8 (Int.zero_ext 8 v))) = Some (Vint (Int.zero_ext 8 v))) end;
            rewrite Int.zero_ext_idem by lia; reflexivity.
        - exact Hwrite. }
      apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k; cbn; split; solve [discriminate|reflexivity].
  - destruct k; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

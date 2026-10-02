(** Actual subtract_8 call, including byte promotions and the signed borrow comparison. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary8_exec C.jet_readBit_layout C.jet_increment8_exec C.jet_add8 C.jet_subtract_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition subtract8_borrow_expr := Ebinop Olt (Etempvar _x tuchar) (Etempvar _y tuchar) tint.
Definition subtract8_payload_expr := Ecast
  (Ebinop Osub (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint)
    (Etempvar _y tuchar) tuint) tuchar.
Definition le_subtract8_x env bd dofs bs sofs r :=
  PTree.set _x (Vint (add8_u r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env f_simplicity_subtract_8 bd dofs bs sofs)).
Definition le_subtract8_y env bd dofs bs sofs r t :=
  PTree.set _y (Vint (add8_u t)) (PTree.set _t'2 (Vint t) (le_subtract8_x env bd dofs bs sofs r)).

Lemma subtract8_body : f_simplicity_subtract_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence (frame_writer_call _writeBit tbool tbool subtract8_borrow_expr)
          (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid subtract8_payload_expr)
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. reflexivity. Qed.

Lemma eval_subtract8_borrow_expr e le m r t :
  le!_x = Some (Vint (add8_u r)) -> le!_y = Some (Vint (add8_u t)) ->
  eval_expr ge0 e le m subtract8_borrow_expr (Vint (bit_int (subtract8_borrow r t))).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vint (add8_u r)) (v2 := Vint (add8_u t)).
  - apply eval_Etempvar. exact HX.
  - apply eval_Etempvar. exact HY.
  - change (Some (Val.of_bool (subtract8_borrow r t)) = Some (Vint (bit_int (subtract8_borrow r t)))).
    destruct (subtract8_borrow r t); reflexivity.
Qed.
Lemma eval_subtract8_payload_expr e le m r t :
  le!_x = Some (Vint (add8_u r)) -> le!_y = Some (Vint (add8_u t)) ->
  eval_expr ge0 e le m subtract8_payload_expr (Vint (subtract8_payload r t)).
Proof.
  intros HX HY. eapply eval_Ecast with
    (v1 := Vint (Int.sub (Int.mul Int.one (add8_u r)) (add8_u t))).
  - eapply eval_Ebinop with (v1 := Vint (Int.mul Int.one (add8_u r))) (v2 := Vint (add8_u t)).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint (add8_u r)).
      * apply eval_Econst_int.
      * apply eval_Etempvar. exact HX.
      * reflexivity.
    + apply eval_Etempvar. exact HY.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eval_subtract8_composes env m ma mc mr mr2 mb me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (subtract8_borrow r t))]
    E0 mb (Vint (bit_int (subtract8_borrow r t))) ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (subtract8_payload r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_subtract_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_subtract_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_subtract8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite subtract8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_subtract8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_subtract8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        assert (HX : (le_subtract8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)!_x = Some (Vint (add8_u r))).
        { unfold le_subtract8_y. rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HY : (le_subtract8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)!_y = Some (Vint (add8_u t)))
          by (apply PTree.gss).
        assert (HDst : (le_subtract8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_subtract8_y, le_subtract8_x, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        { eapply call_frame_writer_cast with (f := f_writeBit)
            (vraw := Vint (bit_int (subtract8_borrow r t)))
            (v := Vint (bit_int (subtract8_borrow r t)))
            (vret := Vint (bit_int (subtract8_borrow r t))).
          - reflexivity.
          - exact HDst.
          - reflexivity.
          - apply symbol_writeBit.
          - apply funct_writeBit.
          - apply eval_subtract8_borrow_expr; assumption.
          - destruct (subtract8_borrow r t); reflexivity.
          - exact Hbit. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        { eapply call_frame_writer with (f := f_simplicity_write8) (v := Vint (subtract8_payload r t)) (vret := Vundef).
          - reflexivity.
          - exact HDst.
          - reflexivity.
          - apply symbol_write8.
          - apply funct_write8.
          - apply eval_subtract8_payload_expr; assumption.
          - unfold subtract8_payload. change
              (Some (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.sub (Int.mul Int.one (add8_u r)) (add8_u t))))) =
                Some (Vint (Int.zero_ext 8 (Int.sub (Int.mul Int.one (add8_u r)) (add8_u t))))).
            rewrite Int.zero_ext_idem by lia. reflexivity.
          - exact Hwrite. }
        apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

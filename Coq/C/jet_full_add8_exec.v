(** The actual short-circuit branch and complete carry-input byte-adder call. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_increment8_exec C.jet_binary1_exec C.jet_binary8_exec C.jet_readBit_layout.
Require Import C.jet_add8 C.jet_full_add8_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_add8_sum_raw_expr := Ebinop Oadd
  (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint)
  (Etempvar _y tuchar) tuint.
Definition full_add8_second_carry_expr := Ebinop Olt
  (Ebinop Osub
    (Ebinop Omul (Econst_int Int.one tuint) (Econst_int (Int.repr 255) tint) tuint)
    (Etempvar _z tbool) tuint) full_add8_sum_raw_expr tint.
Definition full_add8_sum_expr :=
  Ecast (Ebinop Oadd full_add8_sum_raw_expr (Etempvar _z tbool) tuint) tuchar.
Definition full_add8_choose := Sifthenelse add8_carry_expr
  (Sset _t'4 (Econst_int Int.one tint))
  (Sset _t'4 (Ecast full_add8_second_carry_expr tbool)).
Definition le_full_add8_z env bd dofs bs sofs cin :=
  PTree.set _z (Vint (bit_int cin)) (PTree.set _t'1 (Vint (bit_int cin))
    (le_arith8_layout env f_simplicity_full_add_8 bd dofs bs sofs)).
Definition le_full_add8_x env bd dofs bs sofs cin r :=
  PTree.set _x (Vint (add8_u r)) (PTree.set _t'2 (Vint r)
    (le_full_add8_z env bd dofs bs sofs cin)).
Definition le_full_add8_y env bd dofs bs sofs cin r t :=
  PTree.set _y (Vint (add8_u t)) (PTree.set _t'3 (Vint t)
    (le_full_add8_x env bd dofs bs sofs cin r)).
Definition le_full_add8_carry env bd dofs bs sofs cin r t :=
  PTree.set _t'4 (Vint (bit_int (full_add8_carry cin r t)))
    (le_full_add8_y env bd dofs bs sofs cin r t).

Lemma full_add8_body : f_simplicity_full_add_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _z (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _x (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence
          (Ssequence (binary8_read _t'3) (Sset _y (Ecast (Etempvar _t'3 tuchar) tuchar)))
          (Ssequence
            (Ssequence full_add8_choose (frame_writer_call _writeBit tbool tbool (Etempvar _t'4 tint)))
            (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid full_add8_sum_expr)
              (Sreturn (Some (Econst_int Int.one tint)))))))).
Proof. reflexivity. Qed.

Lemma eval_full_add8_sum_raw_expr e le m r t :
  le!_x = Some (Vint (add8_u r)) -> le!_y = Some (Vint (add8_u t)) ->
  eval_expr ge0 e le m full_add8_sum_raw_expr (Vint (add8_sum_raw r t)).
Proof.
  intros HX HY. unfold full_add8_sum_raw_expr, add8_sum_raw.
  eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + apply eval_Econst_int.
    + apply eval_Etempvar. exact HX.
    + reflexivity.
  - apply eval_Etempvar. exact HY.
  - reflexivity.
Qed.
Lemma eval_full_add8_second_carry_expr e le m cin r t :
  le!_z = Some (Vint (bit_int cin)) ->
  le!_x = Some (Vint (add8_u r)) -> le!_y = Some (Vint (add8_u t)) ->
  eval_expr ge0 e le m full_add8_second_carry_expr
    (Vint (bit_int (full_add8_second_carry cin r t))).
Proof.
  intros HZ HX HY. unfold full_add8_second_carry_expr.
  eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
    + apply eval_Etempvar. exact HZ.
    + reflexivity.
  - exact (eval_full_add8_sum_raw_expr e le m r t HX HY).
  - change (Some (Val.of_bool (full_add8_second_carry cin r t)) =
      Some (Vint (bit_int (full_add8_second_carry cin r t)))).
    destruct (full_add8_second_carry cin r t); reflexivity.
Qed.
Lemma eval_full_add8_sum_expr e le m cin r t :
  le!_z = Some (Vint (bit_int cin)) ->
  le!_x = Some (Vint (add8_u r)) -> le!_y = Some (Vint (add8_u t)) ->
  eval_expr ge0 e le m full_add8_sum_expr (Vint (full_add8_payload cin r t)).
Proof.
  intros HZ HX HY. unfold full_add8_sum_expr, full_add8_payload, full_add8_raw.
  eapply eval_Ecast.
  - eapply eval_Ebinop.
    + exact (eval_full_add8_sum_raw_expr e le m r t HX HY).
    + apply eval_Etempvar. exact HZ.
    + reflexivity.
  - reflexivity.
Qed.
Lemma exec_full_add8_choose e le m cin r t :
  le!_z = Some (Vint (bit_int cin)) ->
  le!_x = Some (Vint (add8_u r)) -> le!_y = Some (Vint (add8_u t)) ->
  Clight2.exec_stmt ge0 e le m full_add8_choose E0
    (PTree.set _t'4 (Vint (bit_int (full_add8_carry cin r t))) le) m Out_normal.
Proof.
  intros HZ HX HY. unfold full_add8_choose.
  pose proof (eval_add8_carry_env m e le r t HX HY) as HE.
  change (eval_expr ge0 e le m add8_carry_expr (Vint (bit_int (full_add8_first_carry r t)))) in HE.
  destruct (full_add8_first_carry r t) eqn:Hfirst.
  - unfold full_add8_carry. rewrite Hfirst. change (orb Datatypes.true _) with Datatypes.true.
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HE.
    + reflexivity.
    + apply exec_set. apply eval_Econst_int.
  - unfold full_add8_carry. rewrite Hfirst. change (orb Datatypes.false (full_add8_second_carry cin r t))
      with (full_add8_second_carry cin r t).
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HE.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int (full_add8_second_carry cin r t))).
      * apply eval_full_add8_second_carry_expr; assumption.
      * destruct (full_add8_second_carry cin r t); reflexivity.
Qed.

Lemma eval_full_add8_composes env m ma mc mr mr2 mr3 mb me mf bl bd dbase bs sbase bytes cin r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int cin)) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr3 (Vint t) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (full_add8_carry cin r t))]
    E0 mb (Vint (bit_int (full_add8_carry cin r t))) ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (full_add8_payload cin r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_full_add_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_full_add_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_full_add8_carry env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_z; _x; _y; _t'4; _t'3; _t'2; _t'1]).
    intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; vm_compute in H, H0; congruence.
  - rewrite full_add8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_full_add8_z env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int cin)).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct cin; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_full_add8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint r).
            + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
          (le1 := le_full_add8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_binary8_read. exact Hread3.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint t).
            + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        assert (HZ : (le_full_add8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_z =
          Some (Vint (bit_int cin))).
        { unfold le_full_add8_y, le_full_add8_x, le_full_add8_z.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HX : (le_full_add8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_x =
          Some (Vint (add8_u r))).
        { unfold le_full_add8_y. rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HY : (le_full_add8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_y =
          Some (Vint (add8_u t))) by (apply PTree.gss).
        assert (HDst : (le_full_add8_carry env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_full_add8_carry, le_full_add8_y, le_full_add8_x, le_full_add8_z, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb)
          (le1 := le_full_add8_carry env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
            (le1 := le_full_add8_carry env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t).
          - apply exec_full_add8_choose; assumption.
          - eapply call_frame_writer_cast with (f := f_writeBit)
              (vraw := Vint (bit_int (full_add8_carry cin r t)))
              (v := Vint (bit_int (full_add8_carry cin r t)))
              (vret := Vint (bit_int (full_add8_carry cin r t))).
            + reflexivity.
            + exact HDst.
            + reflexivity.
            + apply symbol_writeBit.
            + apply funct_writeBit.
            + apply eval_Etempvar. apply PTree.gss.
            + destruct (full_add8_carry cin r t); reflexivity.
            + exact Hbit. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        { eapply call_frame_writer with (f := f_simplicity_write8)
            (v := Vint (full_add8_payload cin r t)) (vret := Vundef).
          - reflexivity.
          - exact HDst.
          - reflexivity.
          - apply symbol_write8.
          - apply funct_write8.
          - apply eval_full_add8_sum_expr;
              unfold le_full_add8_carry; rewrite PTree.gso by discriminate; assumption.
          - change (Some (Vint (Int.zero_ext 8 (full_add8_payload cin r t))) =
              Some (Vint (full_add8_payload cin r t))).
            unfold full_add8_payload. rewrite Int.zero_ext_idem by lia. reflexivity.
          - exact Hwrite. }
        apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

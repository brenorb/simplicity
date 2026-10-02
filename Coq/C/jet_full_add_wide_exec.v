(** Actual full_add_16/32/64 bodies and their short-circuit carry branches. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_increment8_exec C.jet_binary1_exec C.jet_binary_wide_exec C.jet_readBit_layout.
Require Import C.jet_full_increment_wide_word C.jet_full_increment_wide_exec C.jet_full_add_wide_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_full_add s := match s with W16 => f_simplicity_full_add_16
  | W32 => f_simplicity_full_add_32 | W64 => f_simplicity_full_add_64 end.
Definition wide_full_add_sum_raw_expr := Ebinop Oadd
  (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong)
  (Etempvar _y tulong) tulong.
Definition wide_full_add_first_carry_expr s := Ebinop Olt
  (Ebinop Osub
    (Ebinop Omul (Econst_int Int.one tuint) (wide_full_increment_limit_expr s)
      (wide_full_increment_limit_type s)) (Etempvar _y tulong) tulong)
  (Etempvar _x tulong) tint.
Definition wide_full_add_second_carry_expr s :=
  Ebinop Olt (wide_full_increment_sub_expr s) wide_full_add_sum_raw_expr tint.
Definition wide_full_add_sum_expr :=
  Ecast (Ebinop Oadd wide_full_add_sum_raw_expr (Etempvar _z tbool) tulong) tulong.
Definition wide_full_add_choose s := Sifthenelse (wide_full_add_first_carry_expr s)
  (Sset _t'4 (Econst_int Int.one tint))
  (Sset _t'4 (Ecast (wide_full_add_second_carry_expr s) tbool)).
Definition le_wide_full_add_z env s bd dofs bs sofs cin :=
  PTree.set _z (Vint (bit_int cin)) (PTree.set _t'1 (Vint (bit_int cin))
    (le_arith8_layout env (wide_full_add s) bd dofs bs sofs)).
Definition le_wide_full_add_x env s bd dofs bs sofs cin r :=
  PTree.set _x (Vlong r) (PTree.set _t'2 (Vlong r)
    (le_wide_full_add_z env s bd dofs bs sofs cin)).
Definition le_wide_full_add_y env s bd dofs bs sofs cin r t :=
  PTree.set _y (Vlong t) (PTree.set _t'3 (Vlong t)
    (le_wide_full_add_x env s bd dofs bs sofs cin r)).
Definition le_wide_full_add_carry env s bd dofs bs sofs cin r t :=
  PTree.set _t'4 (Vint (bit_int (wide_full_add_carry s cin r t)))
    (le_wide_full_add_y env s bd dofs bs sofs cin r t).

Lemma wide_full_add_body s : (wide_full_add s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _z (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _x (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (wide_binary_read s _t'3) (Sset _y (Etempvar _t'3 tulong)))
          (Ssequence
            (Ssequence (wide_full_add_choose s) (frame_writer_call _writeBit tbool tbool (Etempvar _t'4 tint)))
            (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid wide_full_add_sum_expr)
              (Sreturn (Some (Econst_int Int.one tint)))))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_wide_full_add_sum_raw_expr e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m wide_full_add_sum_raw_expr (Vlong (Int64.add r t)).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
    + apply eval_Econst_int.
    + apply eval_Etempvar. exact HX.
    + change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
      rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
  - apply eval_Etempvar. exact HY.
  - reflexivity.
Qed.
Lemma eval_wide_full_add_limit_expr e le m s :
  eval_expr ge0 e le m
    (Ebinop Omul (Econst_int Int.one tuint) (wide_full_increment_limit_expr s)
      (wide_full_increment_limit_type s)) (wide_full_increment_limit_value s).
Proof.
  eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := wide_full_increment_limit_value s).
  - apply eval_Econst_int.
  - destruct s; [apply eval_Econst_int|apply eval_Econst_int|apply eval_Econst_long].
  - destruct s.
    + change (Some (Vint (Int.mul Int.one (Int.repr 65535))) = Some (Vint (Int.repr 65535))).
      rewrite Int.mul_commut, Int.mul_one. reflexivity.
    + change (Some (Vint (Int.mul Int.one Int.mone)) = Some (Vint Int.mone)).
      rewrite Int.mul_commut, Int.mul_one. reflexivity.
    + change (Some (Vlong (Int64.mul Int64.one Int64.mone)) = Some (Vlong Int64.mone)).
      rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
Qed.
Lemma eval_wide_full_add_first_carry_expr e le m s r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m (wide_full_add_first_carry_expr s)
    (Vint (bit_int (wide_full_add_first_carry s r t))).
Proof.
  intros HX HY. eapply eval_Ebinop with
    (v1 := Vlong (Int64.sub (Int64.repr (wide_full_increment_max s)) t)) (v2 := Vlong r).
  - eapply eval_Ebinop with (v1 := wide_full_increment_limit_value s) (v2 := Vlong t).
    + apply eval_wide_full_add_limit_expr.
    + apply eval_Etempvar. exact HY.
    + destruct s; reflexivity.
  - apply eval_Etempvar. exact HX.
  - change (Some (Val.of_bool (wide_full_add_first_carry s r t)) =
      Some (Vint (bit_int (wide_full_add_first_carry s r t)))).
    destruct (wide_full_add_first_carry s r t); reflexivity.
Qed.
Lemma eval_wide_full_add_second_carry_expr e le m s cin r t :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m (wide_full_add_second_carry_expr s)
    (Vint (bit_int (wide_full_increment_carry s cin (Int64.add r t)))).
Proof.
  intros HZ HX HY. eapply eval_Ebinop with (v1 := wide_full_increment_sub_value s cin)
    (v2 := Vlong (Int64.add r t)).
  - apply eval_wide_full_increment_sub_expr. exact HZ.
  - exact (eval_wide_full_add_sum_raw_expr e le m r t HX HY).
  - destruct s, cin.
    all: lazymatch goal with | |- _ = Some (Vint (bit_int ?b)) =>
      change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity end.
Qed.
Lemma eval_wide_full_add_sum_expr e le m cin r t :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m wide_full_add_sum_expr (Vlong (wide_full_add_payload cin r t)).
Proof.
  intros HZ HX HY. eapply eval_Ecast with (v1 := Vlong (wide_full_add_payload cin r t)).
  - eapply eval_Ebinop with (v1 := Vlong (Int64.add r t)) (v2 := Vint (bit_int cin)).
    + exact (eval_wide_full_add_sum_raw_expr e le m r t HX HY).
    + apply eval_Etempvar. exact HZ.
    + destruct cin; reflexivity.
  - reflexivity.
Qed.
Lemma exec_wide_full_add_choose e le m s cin r t :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  Clight2.exec_stmt ge0 e le m (wide_full_add_choose s) E0
    (PTree.set _t'4 (Vint (bit_int (wide_full_add_carry s cin r t))) le) m Out_normal.
Proof.
  intros HZ HX HY. unfold wide_full_add_choose.
  pose proof (eval_wide_full_add_first_carry_expr e le m s r t HX HY) as HE.
  destruct (wide_full_add_first_carry s r t) eqn:Hfirst.
  - unfold wide_full_add_carry. rewrite Hfirst.
    change (orb Datatypes.true _) with Datatypes.true.
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HE.
    + reflexivity.
    + apply exec_set. apply eval_Econst_int.
  - unfold wide_full_add_carry. rewrite Hfirst.
    change (orb Datatypes.false (wide_full_increment_carry s cin (Int64.add r t)))
      with (wide_full_increment_carry s cin (Int64.add r t)).
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HE.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int (wide_full_increment_carry s cin (Int64.add r t)))).
      * apply eval_wide_full_add_second_carry_expr; assumption.
      * destruct (wide_full_increment_carry s cin (Int64.add r t)); reflexivity.
Qed.
Lemma eval_wide_full_add_composes env s m ma mc mr mr2 mr3 mb me mf bl bd dbase bs sbase bytes cin r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int cin)) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong t) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_full_add_carry s cin r t))]
    E0 mb (Vint (bit_int (wide_full_add_carry s cin r t))) ->
  Clight2.eval_funcall ge0 mb (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (wide_full_add_payload cin r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_full_add s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_full_add s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_full_add_carry env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_z; _x; _y; _t'4; _t'3; _t'2; _t'1]);
    intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; vm_compute in H, H0; congruence.
  - rewrite wide_full_add_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_full_add_z env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int cin)).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct cin; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_wide_full_add_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
          (le1 := le_wide_full_add_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_wide_binary_read. exact Hread3.
          - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        assert (HZ : (le_wide_full_add_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_z =
          Some (Vint (bit_int cin))).
        { unfold le_wide_full_add_y, le_wide_full_add_x, le_wide_full_add_z.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HX : (le_wide_full_add_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_x =
          Some (Vlong r)).
        { unfold le_wide_full_add_y. rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HY : (le_wide_full_add_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_y =
          Some (Vlong t)) by (apply PTree.gss).
        assert (HDst : (le_wide_full_add_carry env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_wide_full_add_carry, le_wide_full_add_y, le_wide_full_add_x, le_wide_full_add_z, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb)
          (le1 := le_wide_full_add_carry env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
            (le1 := le_wide_full_add_carry env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r t).
          - apply exec_wide_full_add_choose; assumption.
          - eapply call_frame_writer_cast with (f := f_writeBit)
              (vraw := Vint (bit_int (wide_full_add_carry s cin r t)))
              (v := Vint (bit_int (wide_full_add_carry s cin r t)))
              (vret := Vint (bit_int (wide_full_add_carry s cin r t))).
            + reflexivity.
            + exact HDst.
            + reflexivity.
            + apply symbol_writeBit.
            + apply funct_writeBit.
            + apply eval_Etempvar. apply PTree.gss.
            + destruct (wide_full_add_carry s cin r t); reflexivity.
            + exact Hbit. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        { eapply call_frame_writer with (f := wide_writer s)
            (v := Vlong (wide_full_add_payload cin r t)) (vret := Vundef).
          - destruct s; reflexivity.
          - exact HDst.
          - destruct s; reflexivity.
          - apply wide_writer_symbol.
          - apply wide_writer_funct.
          - apply eval_wide_full_add_sum_expr;
              unfold le_wide_full_add_carry; rewrite PTree.gso by discriminate; assumption.
          - reflexivity.
          - exact Hwrite. }
        apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

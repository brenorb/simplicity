(** Actual byte lt/le: two reads, promoted comparison, bit write and cleanup. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Bit C.jets C.jet_exec C.jet_one8 C.jet_spec.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8_exec.
Require Import C.jet_read8 C.jet_add8_word C.jet_binary8_exec C.jet_readBit_layout.
Require Import C.jet_predicate8_exec C.jet_order_spec C.jet_order_wide_exec C.jet_subtract_word C.jet_add8.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition order8 k := match k with OLt => f_simplicity_lt_8 | OLe => f_simplicity_le_8 end.
Definition order8_expr k := Ebinop (order_binop k) (Etempvar _x tuchar) (Etempvar _y tuchar) tint.
Definition order8_bit k r t := Int.cmp (order_cmp k) (Int.zero_ext 8 r) (Int.zero_ext 8 t).
Definition le_order8_x env k bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (order8 k) bd dofs bs sofs)).
Definition le_order8_y env k bd dofs bs sofs r t :=
  PTree.set _y (Vint (Int.zero_ext 8 t)) (PTree.set _t'2 (Vint t)
    (le_order8_x env k bd dofs bs sofs r)).

Lemma order8_bit_numeric k r t :
  order8_bit k r t = order_numeric k (Int.unsigned (add8_u r)) (Int.unsigned (add8_u t)).
Proof.
  destruct k.
  - apply subtract8_borrow_numeric.
  - change (negb (subtract8_borrow t r) = (Int.unsigned (add8_u r) <=? Int.unsigned (add8_u t))).
    rewrite subtract8_borrow_numeric.
    destruct (Int.unsigned (add8_u t) <? Int.unsigned (add8_u r)) eqn:H;
      [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; cbn [negb]; symmetry;
      [apply Z.leb_gt|apply Z.leb_le]; lia.
Qed.
Lemma order8_denotes k w z :
  order8_bit k (read8_result w) (read8_result z) =
    Bit.toBool (@order_word_spec k 3 Alg.CoreFunSem (decode_word8 w, decode_word8 z)).
Proof.
  rewrite order8_bit_numeric, !read8_result_unsigned, order_word_spec_numeric. reflexivity.
Qed.

Lemma order8_body k : (order8 k).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence (frame_writer_call _writeBit tbool tbool (order8_expr k))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k; reflexivity. Qed.

Lemma eval_order8_expr e le m k r t :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  eval_expr ge0 e le m (order8_expr k) (Vint (bit_int (order8_bit k r t))).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vint (Int.zero_ext 8 r)) (v2 := Vint (Int.zero_ext 8 t)).
  - apply eval_Etempvar; exact HX.
  - apply eval_Etempvar; exact HY.
  - destruct k.
    all: lazymatch goal with | |- _ = Some (Vint (bit_int ?b)) =>
      change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity end.
Qed.

Lemma eval_order8_composes env k m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (order8_bit k r t))] E0 me (Vint (bit_int (order8_bit k r t))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (order8 k))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (order8 k) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_order8_y env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k; reflexivity|destruct k; reflexivity| |exact HA].
    destruct k; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite order8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_order8_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (order8_bit k r t))) (v := Vint (bit_int (order8_bit k r t)))
             (vret := Vint (bit_int (order8_bit k r t))).
           ++ reflexivity.
           ++ unfold le_order8_y, le_order8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_order8_expr.
              ** unfold le_order8_y, le_order8_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_order8_y. rewrite PTree.gss. reflexivity.
           ++ destruct (order8_bit k r t); reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k; cbn; split; solve [discriminate|reflexivity].
  - destruct k; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
